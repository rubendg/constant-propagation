{-# LANGUAGE GADTs #-}
module Monotone.Framework where
import Monotone.Interface
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Monoid
import Debug.Trace
import Data.Maybe (fromJust)

type WorklistEntry ctx = ((ctx, From), (ctx, To)) 
type Worklist ctx = [WorklistEntry ctx]

-- Lifts the original analysis lattice to a lattice with context
instance (Ord ctx, Lattice a) => Lattice (M.Map ctx a) where
  top       = error "no top"
  bottom    = M.empty
  join m m' = M.unionWith join m m'
  meet      = undefined

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
computeFixedPoint flow fspace mutateContext w a =
  (Step (a, a)) : iterate w a
  where 
  iterate w a =
    let (w', st@(Step (a',_))) = step flow fspace mutateContext w a
    in case w' of
        []        -> [st]
        otherwise -> st : iterate w' a'

-- doesn't flow to z=2 after return
-- "function f(){x=0;}z=0;f();z=2;"
-- cannot cope with function call as first instruction
-- function f(){}f();z=0; 

step :: (Show l, Monoid ctx, Ord ctx, Show ctx, Lattice l) => 
     ControlFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> ContextMutator ctx
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, Step ctx l)
step flow fspace mutateContext w a = 
  let (w', a') = step' flow fspace mutateContext w a
  in (w', Step (a', computeEffect a' fspace))

step' :: (Show l, Monoid ctx, Show ctx, Ord ctx, Lattice l) => 
     ControlFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> ContextMutator ctx
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, AnalysisResult ctx l)
step' _              _      _             [] analysis = ([], analysis)
step' flow@(_,inter) fspace mutateContext w  analysis =
  let ((previousContext, from), (context, to)) = head w
      rest                                     = tail w
      entry                                    = analysis `fapp` from
      oldExit                                  = (analysis `fapp` to) `fapp` context
      lblTy                                    = transferType flow to
      lblTy'                                   = case lblTy of 
                                                  Exit _ -> Normal
                                                  otherwise -> lblTy
  in traceShow ("worklist: " ++ show w) (
     case lblTy of
      Normal -> 
        let exit' = transferUnary fspace from entry previousContext
        in
          -- if the previously known exit value of the node pointed to is not more precise than
          -- newly calculated exit we need to update the exit value by joining the old and new
          -- exit value and add all successors to the worklist such that they can be made consistent
          -- with the new exit value in future iterations.
          traceShow ("normal: " ++ show exit' ++ "/= " ++ show oldExit) (
          if exit' /= oldExit
            then let successors = succWorklist flow to context
                     newExit    = oldExit `join` exit'
                     analysis'  = M.insert to (M.insert context newExit entry) analysis
                 in trace ("normal: insert into " ++ show context ++ "new: " ++ show newExit ++ "entry: " ++ show entry) 
                    (successors ++ rest, analysis')
            else (rest, analysis) )

      Call (callLbl,entryLbl,exitLbl,returnLbl) ->    
        let exit'      = transferUnary fspace from entry context
            newExit    = oldExit `join` exit'
            analysis'  = M.insert to (M.insert context newExit entry) analysis
            newContext = mutateContext from context
            w'         = ((newContext, exitLbl), (context, returnLbl))
            w''        = ((context, callLbl), (newContext, entryLbl))
        in trace ("call: insert into " ++ show newContext ++ "new: " ++ show newExit ++ "entry: " ++ 
           show entry ++ show (M.insert newContext newExit entry)) 
           (w'' : w' : rest, analysis')

      Entry _ -> 
        let exit = transferUnary fspace from entry previousContext 
            analysis' = M.insert to (M.insert context exit (analysis `fapp` to)) analysis         
        in traceShow ("entry: " ++ show context ++ "effect: " ++ show exit ++ "entry: " ++ show entry) 
           ((succWorklist flow to context) ++ rest, analysis')

      Exit _ ->
        let exit'     = join ((analysis `fapp` from) `fapp` previousContext)
                             ((analysis `fapp` to) `fapp` context)
            -- transferBinary fspace to callLbl returnLbl (fapp $ analysis `fapp` from) (fapp $ analysis `fapp` to) context
            analysis' = M.insert to (M.insert context exit' (analysis `fapp` to)) analysis
        in traceShow ("exit: " ++ show context ++ ": " ++ show (M.insert context exit' entry)) 
           ((succWorklist flow to context) ++ rest, analysis')

      Return (callLbl,_,_,returnLbl) -> 
        let exit = transferUnary fspace from entry previousContext 
            analysis' = M.insert to (M.insert context exit (analysis `fapp` to)) analysis
        in traceShow ("return: " ++ show context ++ "effect: " ++ show exit ++ "entry: " ++ show entry) 
           (rest, analysis')
{-
        let exit'     = join ((analysis `fapp` from) `fapp` previousContext)
                             ((analysis `fapp` to) `fapp` context)
            -- transferBinary fspace to callLbl returnLbl (fapp $ analysis `fapp` from) (fapp $ analysis `fapp` to) context
            analysis' = M.insert to (M.insert context exit' (analysis `fapp` to)) analysis
        in traceShow ("return: " ++ show context ++ ": " ++ show (M.insert context exit' entry)) 
           ((succWorklist flow to context) ++ remainingWork, analysis')
-}
    )

transferUnary fspace lbl l ctx =
  let Left transfer = fspace lbl
  in traceShow ("tranfer(" ++ show lbl ++ ")") transfer lbl (fapp l) ctx

transferBinary fspace lbl lbl1 lbl2 l l' ctx = 
  let Right transfer = fspace lbl
  in transfer lbl1 lbl2 l l' ctx

data TransferType = Normal 
                  | Call InterFlowEntry
                  | Entry InterFlowEntry
                  | Exit InterFlowEntry
                  | Return InterFlowEntry
  deriving Show


transferType (_,inter) lbl = foldr (lblToType lbl) Normal inter
   where
   lblToType lbl i@(c,n,e,r) = 
    case xs of
      []        -> id
      otherwise -> const (snd (head xs))
    where
    mapping = [(c,Call i),(n,Entry i),(e,Exit i),(r,Return i)]
    xs      = filter (\x -> fst x == lbl) mapping

{-
transferType (_,inter) lbl = foldr (lblToType lbl) Normal inter
  where
  lblToType lbl i@(c,n,e,r) = 
    if lbl == (c,n)
      then const (Call i)
      else if lbl == (e,r)
            then const (Exit i)
            else id
-}

-- does not take ctx change into account
succWorklist :: ControlFlow n -> Label -> ctx -> Worklist ctx 
succWorklist flow lbl ctx =
 let node       = (ctx, lbl)
     successors = suc flow lbl
  in map (\suc -> (node, (ctx, suc))) successors

computeEffect :: (Ord ctx, Lattice l) => AnalysisResult ctx l -> TransferFunctionSpaceMapping ctx l -> AnalysisResult ctx l
computeEffect a fspace = M.mapWithKey transfer a
  where
  transfer lbl l = 
    case fspace lbl of
      Left tf  -> M.mapWithKey (\ctx _ -> tf lbl (fapp l) ctx) l 
      Right tf -> l -- "not yet implemented"

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

