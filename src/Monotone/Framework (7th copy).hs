{-# LANGUAGE GADTs #-}
module Monotone.Framework where
import Monotone.Interface
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Monoid
import Data.List (unfoldr)
import Debug.Trace 
import Data.Maybe (fromJust)

type WorklistEntry ctx = ((ctx, From), (ctx, To)) 
type Worklist ctx = [WorklistEntry ctx]

-- Lifts the original analysis lattice to a lattice with context
instance (Ord ctx, Lattice a) => Lattice (M.Map ctx a) where
  top       = error "no explicit top, top is set union closed by the possible contexts"
  bottom    = M.empty
  join m m' = M.unionWith join m m'

-- there can only be one extremalLabel right?
maximalFixedPoint' :: (Show l, Monoid ctx, Show ctx, Ord ctx, Lattice l) => MonotoneFramework ctx n l -> [Step ctx l]
maximalFixedPoint' (MF (extremalLabel, extremalValue, fspace, flow, mutateContext, ctx)) = 
  let 
      -- initialize the nodes corresponding with the extremal labels to
      -- the extremal value, otherwise to bottom.
      yota = if ctx == mempty
              then M.singleton ctx extremalValue
              else bottom

      initialLattice =
        let initialize l | l == extremalLabel = (l, yota)
                         | otherwise          = (l, bottom)
        in M.fromList $ map initialize (nodes flow)

      -- all, or only the first?
      worklist = succWorklist flow extremalLabel ctx

  in computeFixedPoint flow fspace mutateContext worklist initialLattice

maximalFixedPoint :: (Show l, Monoid ctx, Show ctx, Ord ctx, Lattice l) => MonotoneFramework ctx n l -> MFP ctx l
maximalFixedPoint mf = last (maximalFixedPoint' mf)

computeFixedPoint :: (Show l, Ord ctx, Show ctx, Monoid ctx, Lattice l) => 
     ControlFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> ContextMutator ctx
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> [Step ctx l]
computeFixedPoint flow fspace mutateContext w a = unfoldr f (w,a)
  where 
  f ([],_) = Nothing
  f (w,a)  = let (w', a') = step flow fspace mutateContext w a
                 effect   = computeEffect flow fspace mutateContext a'
             in case w' of
                 []        -> Just $ (Step (a', effect), ([],M.empty))
                 otherwise -> Just $ (Step (a', effect), (w',a'))

computeEffect :: (Ord ctx, Lattice l) => 
  ControlFlow n -> 
  TransferFunctionSpaceMapping ctx l -> 
  ContextMutator ctx -> 
  AnalysisResult ctx l -> 
  AnalysisResult ctx l
computeEffect flow@(intra,inter) fspace mutateContext a = M.mapWithKey transfer a
  where
  transfer lbl ctxLat = 
    let handleUnary ((c,_,_,r):_) tf | lbl == c  = M.mapKeys (mutateContext c) (M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat)
                                     | lbl == r  = M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat
                                     | otherwise = M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat
        handleUnary []            tf             = M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat

        handleBinary ((c,_,e,_):_) tf = let call = a `fapp` c
                                            exit = a `fapp` e
                                        in M.mapWithKey (\ctx _ -> tf (fapp call) (fapp exit) ctx) ctxLat
        handleBinary []            _  = error "dark corner"

        interEntry = interLookup lbl inter

    in either (handleUnary interEntry) (handleBinary interEntry) (fspace lbl) 

step :: (Show l, Monoid ctx, Show ctx, Ord ctx, Lattice l) => 
     ControlFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> ContextMutator ctx
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, AnalysisResult ctx l)
step _              _      _             [] analysis = ([], analysis)
step flow@(_,inter) fspace mutateContext w  analysis =
  let ((previousContext, from), (context, to)) = head w

      rest = tail w

      -- Analysis effect: from, i.e. A_effect(from)
      fromEntry = analysis `fapp` from

      -- Analysis context (previous): to, i.e. A_context(to)
      toNode = analysis `fapp` to

      toEntry = toNode `fapp` context

  in traceShow ("worklist[" ++ show w ++ "]" ++ "transfer: " ++ (show $ transferType flow from to)) (
     case transferType flow from to of
      Intra -> 
        let fromExit = transferUnary fspace from fromEntry previousContext
        in
          -- if the previously known exit value of the node pointed to is not more precise than
          -- newly calculated exit we need to update the exit value by joining the old and new
          -- exit value and add all successors to the worklist such that they can be made consistent
          -- with the new exit value in future iterations.
          if fromExit /= toEntry
            then let -- the successors affected by the inconsistency
                     successors = succWorklist flow to context

                     -- join the old with the new information about to's context.
                     newToEntry = fromExit `join` toEntry
                  
                     -- update the analysis result with the new information
                     analysis'  = M.insert to (M.insert context newToEntry toNode) analysis

                 in (successors ++ rest, analysis')
            else (rest, analysis)

      BeforeCall (callLbl,entryLbl,exitLbl,returnLbl) ->
        let fromExit   = transferUnary fspace from fromEntry previousContext
            newToEntry = fromExit `join` toEntry
            analysis'  = M.insert to (M.insert context newToEntry toNode) analysis
            newContext = mutateContext callLbl context
            w'         = ((context, callLbl), (newContext, entryLbl))
        in (w' : rest, analysis')

      Call (callLbl,entryLbl,exitLbl,returnLbl) ->    
        let fromExit   = transferUnary fspace from fromEntry previousContext
            newToEntry = fromExit `join` toEntry
            analysis'  = M.insert to (M.insert context newToEntry toNode) analysis
            w'         = ((context, exitLbl), (previousContext, returnLbl))
        in ((succWorklist flow to context) ++ (w' : rest), analysis')
{-
      Entry _ -> 
        let fromExit = transferUnary fspace from fromEntry previousContext 
            analysis' = M.insert to (M.insert context fromExit toNode) analysis         
        in ((succWorklist flow to context) ++ rest, analysis')
-}
      Exit _ ->
        let fromExit = transferUnary fspace from fromEntry previousContext
            newToEntry = fromExit `join` toEntry
            analysis' = M.insert to (M.insert context newToEntry fromEntry) analysis
        in ((succWorklist flow to context) ++ rest, analysis')

      Return (callLbl,_,_,_) ->
        let fromExit  = transferBinary fspace to (analysis `fapp` callLbl) fromEntry context
            analysis' = M.insert to (M.insert context fromExit toNode) analysis
        in ((succWorklist flow to context) ++ rest, analysis')
{-
      AfterReturn ->
        let fromExit  = (liftUnary id) (fapp fromEntry) previousContext
            analysis' = M.insert to (M.insert context fromExit toNode) analysis
        in ((succWorklist flow to context) ++ rest, analysis')
-}
    )

transferUnary fspace lbl l ctx =
  let Left transfer = fspace lbl
  in transfer (fapp l) ctx

transferBinary fspace lbl l l' ctx = 
  let Right transfer = fspace lbl
  in transfer (fapp l) (fapp l') ctx

data TransferType = Intra 
                  | Call InterFlowEntry
                  | Entry InterFlowEntry
                  | Exit InterFlowEntry
                  | Return InterFlowEntry
                  | BeforeCall InterFlowEntry
                  | AfterReturn
  deriving Show

transferType (intra,inter) from to =
  case matchInterflow inter from to of
    Just x  -> x
    Nothing -> Intra 

matchInterflow inter from to = foldr f Nothing inter
  where 
  f i@(c,n,e,r) | (from,to) == (c,n) = const (Just $ Call i)
                | (from,to) == (e,r) = const (Just $ Return i)
                | to == c            = const (Just $ BeforeCall i)
                | to == e            = const (Just $ Exit i)
                -- | from == n          = const (Just $ Entry i)
                -- | from == r          = const (Just $ AfterReturn)
                | otherwise          = id

interLookup lbl inter = filter pred inter
  where
  pred (c,n,e,r) = c == lbl || n == lbl || e == lbl || r == lbl

succWorklist :: ControlFlow n -> Label -> ctx -> Worklist ctx 
succWorklist flow lbl ctx =
 let node       = (ctx, lbl)
     successors = suc flow lbl
  in map (\suc -> (node, (ctx, suc))) successors

edges (IntraFlow flow,_) = G.edges flow

nodes (IntraFlow flow,_) = G.nodes flow

suc (IntraFlow flow,_) n = G.suc flow n

mkFlowGraph :: IntraFlow n -> InterFlow -> FlowGraph n
mkFlowGraph intra inter = (intra,inter)

-- | Creates a function out of a Data.Map from some value to a lattice element.
--   In case the element is not in the domain, bottom is returned.
fapp :: (Ord a, Lattice l) => M.Map a l -> a -> l
fapp f a = case M.lookup a f of
            Just l  -> l
            Nothing -> bottom

