module Monotone.Framework where
import Monotone.Interface
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Monoid
import Data.List (unfoldr)
import Debug.Trace 
import Data.Maybe (fromJust)

-- The worklist maintains the work that still has to be done. 
-- An atomic unit of work is represented by an edge with context attached. 
type WorklistEntry ctx = ((ctx, From), (ctx, To)) 
type Worklist ctx = [WorklistEntry ctx]

-- Lifts the original analysis lattice to a lattice with context
instance (Ord ctx, Lattice a) => Lattice (M.Map ctx a) where
  top       = error "no explicit top, top is set union closed by the possible contexts"
  bottom    = M.empty
  join m m' = M.unionWith join m m'

-- | Given an instance of the monotone framework this function computes the maximal fixed point 
--   while maintaining all intermediate iteration steps.
maximalFixedPoint' :: (G.Graph gr, Monoid ctx, Ord ctx, Lattice l) => MonotoneFramework gr ctx n l -> [Step ctx l]
maximalFixedPoint' (MF (extremalLabel, extremalValue, fspace, flow@(intra,_), mutateContext)) = 
  let 
      -- the extremal value for the initial context
      yota = M.singleton mempty extremalValue

      -- initialize all program points with bottom, unless the program point
      -- is an extremal label.
      analysis =
        let initialize l | l == extremalLabel = (l, yota)
                         | otherwise          = (l, bottom)
        in M.fromList $ map initialize (G.nodes intra)

      -- Initialize the worklist with the first work item. Because the first
      -- program point is always a skip we can assume that the context is the
      -- empty context.
      worklist = successors flow extremalLabel mempty

  in computeFixedPoint flow fspace mutateContext worklist analysis

-- | Calculates the maximal fixed point given an instance of the monotone framework.
maximalFixedPoint :: (G.Graph gr, Show l, Monoid ctx, Show ctx, Ord ctx, Lattice l) => MonotoneFramework gr ctx n l -> MFP ctx l
maximalFixedPoint mf = last (maximalFixedPoint' mf)

-- | Helper function of maximalFixedPoint'. Performs the actual iteration
--   until a fixed point is reached; indicated by an empty worklist. 
computeFixedPoint :: (G.Graph gr, Ord ctx, Monoid ctx, Lattice l) => 
     FlowGraph gr n
  -> TransferFunctionSpace ctx l
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

-- | Computes the effect value of an analysis result by mapping the transfer functions
--   over all analysis results. It also makes sure that the effect values end-up in the
--   right context, i.e. it might be the case that effect value ends up in a different
--   context than the original context value resided.
computeEffect :: (G.Graph gr, Ord ctx, Lattice l) => 
  FlowGraph gr n -> 
  TransferFunctionSpace ctx l -> 
  ContextMutator ctx -> 
  AnalysisResult ctx l -> 
  AnalysisResult ctx l
computeEffect flow@(intra,inter) fspace mutateContext a = M.mapWithKey transfer a
  where
  transfer lbl ctxLat = 
    let handleUnary ((c,_,_,_):_) tf | lbl == c  = M.mapKeys (mutateContext c) (M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat)
                                     | otherwise = M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat
        handleUnary []            tf             = M.mapWithKey (\ctx _ -> tf (fapp ctxLat) ctx) ctxLat

        handleBinary ((c,_,e,_):_) tf = let call = a `fapp` c
                                            exit = a `fapp` e
                                        in M.mapWithKey (\ctx _ -> tf (fapp call) (fapp exit) ctx) ctxLat
        handleBinary []            _  = error "impossible, dark corner"

        interEntry = interLookup lbl inter

    in either (handleUnary interEntry) (handleBinary interEntry) (fspace lbl) 

-- | The workhorse. Performs a single iteration step. A step is
--   concerned only with the head of the worklist and applies the appropriate
--   transfer function to get from the effect value of particular program point 
--   to the context value of the next program point. Subsequently all
--   edges affected by the change are added to the worklist to be re-evaluated in 
--   future steps.
step :: (G.Graph gr, Monoid ctx, Ord ctx, Lattice l) => 
     FlowGraph gr n
  -> TransferFunctionSpace ctx l
  -> ContextMutator ctx
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, AnalysisResult ctx l)
step _                  _      _             [] analysis = ([], analysis)
step flow@(intra,inter) fspace mutateContext w  analysis =
  let ((previousContext, from), (context, to)) = head w

      rest = tail w

      -- Analysis effect: from, i.e. A_effect(from)
      fromEntry = analysis `fapp` from

      -- Analysis context (previous): to, i.e. A_context(to)
      toNode = analysis `fapp` to

      toEntry = toNode `fapp` context

      -- the possibly new context value 
      fromExit =
        let unaryTransfer  tf  Nothing       = tf (fapp fromEntry) previousContext
            binaryTransfer tf (Just callLbl) = tf (fapp (analysis `fapp` callLbl)) (fapp fromEntry) context
        in case (fspace from, fspace to) of
            (_, Right tf)     -> binaryTransfer tf
            (Left tf, _)      -> unaryTransfer tf
            (Right _, Left _) -> const ((liftUnary id) (fapp fromEntry) previousContext)

  in case transferType flow from to of
      Intra -> 
          -- if the newly calculated context is not equal to the previously known context 
          -- then we the new context value has moved up in the lattice and we have to join
          -- then new with the old context. All edges affected by this change need to be added
          -- to the worklist such that the changes in the context can be propagated in future
          -- steps.
          if (fromExit Nothing) /= toEntry
            then let -- the successors affected by the inconsistency
                     affectedByChange = successors flow to context

                     -- join the old with the new context
                     newToEntry = (fromExit Nothing) `join` toEntry
                  
                     -- update the analysis result with the new information
                     analysis'  = M.insert to (M.insert context newToEntry toNode) analysis

                 in (affectedByChange ++ rest, analysis')
            else (rest, analysis)

      -- if we reached a call we need to perform the transfer and append the interflow
      -- edges to the worklist such that the next action in the upcoming step is
      -- to transfer into the function. This also ensures that somewhere in the future we also transfer back
      -- to the calling site, in effect simulating call stack behavior.
      Call (callLbl,entryLbl,exitLbl,returnLbl) ->    
        let newToEntry = (fromExit Nothing) `join` toEntry
            analysis'  = M.insert to (M.insert context newToEntry toNode) analysis
            newContext = mutateContext callLbl context
            w'         = ((newContext, exitLbl), (previousContext, returnLbl))
            w''        = ((context, callLbl), (newContext, entryLbl))
        in (w'' : w' : rest, analysis')

      -- when returning from a function we apply the transfer function to two lattices instead of one, namely
      -- the one just before the call and the one at function exit. The underlying transfer function
      -- determines what it does with this information. We simply insert the result into the lattice.
      Return (callLbl,_,_,_) ->
        let analysis' = M.insert to (M.insert context (fromExit (Just callLbl)) toNode) analysis
        in ((successors flow to context) ++ rest, analysis')

data TransferType = Intra 
                  | Call InterFlowEntry
                  | Return InterFlowEntry
  deriving Show

transferType (intra,inter) from to =
  case matchInterflow inter from to of
    Just x  -> x
    Nothing -> Intra 

matchInterflow inter from to = foldr f Nothing inter
  where 
  f i@(c,n,e,r) | (from,to) == (e,r) = const (Just $ Return i)
                | to == c            = const (Just $ Call i)
                | otherwise          = id

interLookup lbl inter = filter pred inter
  where
  pred (c,n,e,r) = c == lbl || n == lbl || e == lbl || r == lbl

-- | Find the successors for a particular program point
successors :: G.Graph gr => FlowGraph gr n -> ProgramPoint -> ctx -> Worklist ctx 
successors flow@(intra,inter) lbl ctx =
 let from     = (ctx, lbl)
     intraSuc = G.suc intra lbl

     interSucc []                        = []
     interSucc ((c,n,e,r):_) | c == lbl  = [((ctx, c), (ctx, n))]
                             | otherwise = []

  in map (\suc -> (from, (ctx, suc))) intraSuc ++
     interSucc (interLookup lbl inter)

mkFlowGraph :: G.Graph gr => IntraFlow gr n -> InterFlow -> FlowGraph gr n
mkFlowGraph intra inter = (intra,inter)

-- | Creates a function out of a Data.Map from some value to a lattice element.
--   In case the element is not in the domain, bottom is returned.
fapp :: (Ord a, Lattice l) => M.Map a l -> a -> l
fapp f a = case M.lookup a f of
            Just l  -> l
            Nothing -> bottom

