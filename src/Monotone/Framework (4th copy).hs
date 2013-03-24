{-# LANGUAGE GADTs #-}
module Monotone.Framework where
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Monoid
import Debug.Trace
import Data.Maybe (fromJust)

class Ord a => Lattice a where
  top     :: a
  bottom  :: a
  join    :: a -> a -> a
  meet    :: a -> a -> a

-- Lifts the original analysis lattice to a lattice with context
instance (Ord ctx, Lattice a) => Lattice (M.Map ctx a) where
  top       = error "no top"
  bottom    = M.empty
  join m m' = M.unionWith join m m'
  meet      = undefined

-- tag for interflow
data I = C | R
  deriving Show

type Label = Int
type EdgeLabel = Either () I
type LabeledEdges = [(G.Node,G.Node,EdgeLabel)]
type InterFlow = [(Label,Label,Label,Label)]
type FlowGraph n = (IntraFlow n, InterFlow)
type ControlFlow a = (IntraFlow a,InterFlow)

-- | hide the type of the graph implementation since we don't care about it
data IntraFlow a where
  IntraFlow :: G.Graph gr => gr a EdgeLabel -> IntraFlow a

-- Transfer function types
type F a l = M.Map a l
type CtxInsUnaryTransfer l = Label -> l -> l
type CtxInsBinaryTransfer l = Label -> Label -> l -> l -> l
type CtxSenUnaryTransfer ctx l = Label -> ctx -> F ctx l -> F ctx l
type CtxSenBinaryTransfer ctx l =  Label -> Label -> F ctx l -> F ctx l -> F ctx l
type TransferFunctionSpace ctx l = Either (CtxSenUnaryTransfer ctx l) (CtxSenBinaryTransfer ctx l)
type TransferFunctionSpaceMapping ctx l = Label -> TransferFunctionSpace ctx l

-- The embellished monotone framework
data (Ord ctx, Monoid ctx, Lattice l) => MonotoneFramework ctx node l =
  MF ( ExtremalLabels
     , l
     , TransferFunctionSpaceMapping ctx l
     , FlowGraph node
     , ctx
     )

type ExtremalLabels = S.Set Label
type AnalysisResult ctx l = M.Map Label (M.Map ctx l)
data Step ctx l = Step (AnalysisResult ctx l, AnalysisResult ctx l)
type MFP ctx l = Step ctx l

maximalFixedPoint' :: (Monoid ctx, Ord ctx, Lattice l) => MonotoneFramework ctx n l -> [Step ctx l]
maximalFixedPoint' (MF (extremalLabels, extremalValue, fspace, (intra,inter), ctx)) = 
  let 
      -- initialize the nodes corresponding with the extremal labels to
      -- the extremal value, otherwise to bottom.
      lat = M.singleton mempty extremalValue

      initialLattice =
        let initialize l | l `S.member` extremalLabels = (l, lat)
                         | otherwise                   = (l, bottom)
        in M.fromList $ map initialize (nodes intra)
   
  in computeFixedPoint intra fspace ((labEdges intra),mempty,mempty) initialLattice

maximalFixedPoint :: (Monoid ctx, Ord ctx, Lattice l) => MonotoneFramework ctx n l -> MFP ctx l
maximalFixedPoint mf = last (maximalFixedPoint' mf)   

computeFixedPoint :: (Ord ctx, Monoid ctx, Lattice l) => 
     IntraFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> [Step ctx l]
computeFixedPoint flow fspace w a =
  let (w'@(edges', pctx, ctx), st@(Step (a',_))) = step flow fspace w a
  in case edges' of
      []        -> [st]
      otherwise -> st : computeFixedPoint flow fspace w' a'

step :: (Monoid ctx, Ord ctx, Lattice l) => 
     IntraFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, Step ctx l)
step flow fspace w a = 
  let (w', a') = step' flow fspace w a
  in (w', Step (a',computeEffect a' fspace))

type Worklist ctx = (LabeledEdges, ctx, ctx)

step' :: (Monoid ctx, Ord ctx, Lattice l) => 
     IntraFlow n
  -> TransferFunctionSpaceMapping ctx l
  -> Worklist ctx
  -> AnalysisResult ctx l
  -> (Worklist ctx, AnalysisResult ctx l)
step' _    _      ([], pctx, ctx)      a = (([], pctx, ctx), a)
step' flow fspace w@(edges, pctx, ctx) a =
  let (from, to, lbl) = head edges
      remainingWork   = tail edges
      l               = a `fapp` from
      entry           = (a `fapp` from) -- `fapp` ctx
      exit            = (a `fapp` to) -- `fapp` ctx
  in case lbl of
      Left () -> let effect = let Left transfer = fspace from
                              in transfer from ctx entry
                 in
                  if not (effect <= exit)
                    then let successors = [ (to,to',ty) | (to',ty) <- lsuc flow to ]
                             a'         = M.insert to (M.insert ctx (exit `join` effect) l) a
                         in ((successors ++ remainingWork, pctx, ctx), a')
                    else (w, a)
      Right C -> error "" {-let Left transferCall = fspace from
                 in transferCall from aL effect l_c = call transfer for call
                 ctx_n = join effect for all calls to p (how to get all calls to p..)
                 transfer value at entry -}
        -- entry, take the join over all callers
      Right R -> error "return from function not supported"

computeEffect :: Lattice l => AnalysisResult ctx l -> TransferFunctionSpaceMapping ctx l -> AnalysisResult ctx l
computeEffect a fspace = M.mapWithKey transfer a
  where
  transfer lbl l = 
    let Left tf = fspace lbl
    in transferAllContexts (tf lbl) l

labEdges (IntraFlow flow) = G.labEdges flow

nodes (IntraFlow flow) = G.nodes flow

lsuc (IntraFlow flow) n = G.lsuc flow n

-- | Lifts a context-less unary transfer function to a context-aware unary transfer function
--   but leaves the underlying transfer function as is.
liftUnary :: (Ord ctx, Lattice l) => CtxInsUnaryTransfer l -> CtxSenUnaryTransfer ctx l
liftUnary f = \lbl _ l -> (f lbl) l

transferAllContexts :: Lattice l => (ctx -> F ctx l -> F ctx l) -> F ctx l -> F ctx l
transferAllContexts tf l = M.mapWithKey tf l


-- | Function application lifted to maps. If there exists no 
--   mapping from a to l then bottom is returned.
fapp :: (Ord a, Lattice l) => F a l -> a -> l
fapp f a = case M.lookup a f of
            Just l  -> l
            Nothing -> bottom

mkFlowGraph :: IntraFlow n -> InterFlow -> FlowGraph n
mkFlowGraph intra inter = (intra,inter)

flatten :: (Ord ctx, Lattice l) => MFP ctx l -> ([(Label,ctx,l)],[(Label,ctx,l)])
flatten (Step (c,e)) = (M.foldWithKey f [] c, M.foldWithKey f [] e)
  where
  f k a r = let xs = M.toList a
            in (foldr (\(ctx,l) -> (:) (k,ctx,l)) [] xs) ++ r

instance (Ord ctx, Show ctx, Lattice l, Show l) => Show (Step ctx l) where
  show step = 
    let (c,e) = flatten step
    in "context\n" ++ (render_ c) ++ "\neffect\n" ++ (render_ e)

  showList xs s = 
    let f (l,a) b = "iteration " ++ (show l) ++ "\n" ++ (show a) ++ "\n" ++ b
    in s ++ (foldr f "" (zip [0..] xs)) 

render_ :: (Show l, Show ctx, Ord ctx) => [(Label,ctx,l)] -> String
render_ m = foldr f "" m
  where
  f (lbl,ctx,l) result = "Lbl " ++ (show lbl) ++ " in " ++ (show ctx) ++ ": {" ++ (show l) ++ "}\n" ++ result



