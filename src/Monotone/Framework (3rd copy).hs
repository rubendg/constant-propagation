{-# LANGUAGE MultiParamTypeClasses, ExistentialQuantification, GADTs, FlexibleContexts #-}
module Monotone.Framework where
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Maybe (fromJust)

class Ord a => Lattice a where
  top     :: a
  bottom  :: a
  join    :: a -> a -> a
  meet    :: a -> a -> a


instance (Ord ctx, Lattice a) => Lattice (M.Map ctx a) where
  top       = error "no top"
  bottom    = M.empty
  join m m' = M.unionWith join m m'
  meet      = undefined

type ContextLattice ctx a = Lattice (M.Map ctx a)

data IntraFlow a where
  IntraFlow :: G.Graph gr => gr a EdgeLabel -> IntraFlow a

type InterFlow = [(Label,Label,Label,Label)]
type ControlFlow a = (IntraFlow a,InterFlow)

type EdgeLabel = Either () I

-- tag for interflow
data I = I
  deriving Show

data Lattice lat => MonotoneFramework ctx node lat = 
    MonotoneFramework { extremalLabels    :: ExtremalLabels
                      , extremalValues    :: ExtremalValue lat
                      , transferFunctions :: Label -> ContextTransferFunc (ContextLattice ctx lat)
                      , flowGraph         :: FlowGraph node
                      , initialContext    :: ctx
                      }

data FlowGraph a = FlowGraph { intraFlow :: IntraFlow a
                             , interFlow :: InterFlow 
                             }

data Lattice a => Context a = Context (M.Map Label a)
data Lattice a => Effect a  = Effect (M.Map Label a)

data Lattice a => MFP a = MFP { context :: Context a
                              , effect  :: Effect a
                              }

data Lattice a => TransferFunc a = TransferFunc { primTransfer :: a -> a }

data Lattice a => ContextTransferFunc c a = ContextTransferFunc { transfer :: (c -> a) -> (c -> a) }

liftT :: Lattice a => TransferFunc a -> ContextTransferFunc c a
liftT (TransferFunc f) = ContextTransferFunc $ \l c -> f (l c)

type ExtremalLabels = S.Set Label
data ExtremalValue a = ExtremalValue a

type Label = Int
type LabeledEdges = [(G.Node,G.Node,EdgeLabel)]

flatten :: Lattice a => MFP a -> ([(Label,a)],[(Label,a)])
flatten mfp = let (Context c) = context mfp
                  (Effect e)  = effect mfp
              in (M.toList c, M.toList e)

mkFlowGraph :: IntraFlow n -> InterFlow -> FlowGraph n
mkFlowGraph intra inter = FlowGraph { intraFlow = intra, interFlow = inter }

computeMaximalFixedPoint :: Lattice a => MonotoneFramework [Int] n a -> MFP a
computeMaximalFixedPoint = maximalFixedPoint

maximalFixedPoint :: Lattice a => MonotoneFramework [Int] n a -> MFP a
maximalFixedPoint framework =
  let e                    = extremalLabels framework
      ctx                  = initialContext framework
      yota                 = let (ExtremalValue i) = extremalValues framework
                             in case ctx of
                                  []        -> i
                                  otherwise -> bottom 
      tfFunc               = transferFunctions framework
      fg                   = flowGraph framework
      intraF               = intraFlow fg 

      -- initialize the nodes corresponding with the extremal labels to
      -- the extremal value, otherwise to bottom.
      a = let initialize l | l `S.member` e = (l, yota)
                           | otherwise      = (l, bottom)
          in M.fromList $ map initialize (nodes intraF)
           
  in go step intraF tfFunc (labEdges intraF) ctx a

go step flow transferFunctions w ctx a = 
  let (w', ctx', a') = step flow transferFunctions w ctx a
  in case w' of
      []         -> let effect = M.mapWithKey (\l v -> (transfer (transferFunctions l)) (\_ -> v) ctx') a' 
                    in MFP (Context a') (Effect effect)
      otherwise  -> go step flow transferFunctions w' ctx' a'


labEdges (IntraFlow flow) = G.labEdges flow
nodes (IntraFlow flow) = G.nodes flow
lsuc (IntraFlow flow) n = G.lsuc flow n

{-
fixedPoint flow transferFunctions w ctx a = 
  let (w', a') = step flow transferFunctions w ctx a
  in case w' of
      [] -> let effect = M.mapWithKey (\l v -> transfer (transferFunctions l) v) a' 
            in MFP (Context a') (Effect effect)
      _  -> fixedPoint flow transferFunctions w' ctx a'

fixedPointWithHistory flow transferFunctions iw ctx ia =
  [MFP (Context ia) (Effect ia)] ++ performIteration iw ctx ia
  where
  performIteration w ctx a = 
    let (w', ctx, a') = step flow transferFunctions w ctx a
        effect   = M.mapWithKey (\l v -> transfer (transferFunctions l) v) a'
    in case w' of
        [] -> [MFP (Context a') (Effect effect)]
        _  -> [MFP (Context a') (Effect effect)] ++ (performIteration w' ctx a')
-}

step :: Lattice a => 
     IntraFlow n
  -> (Label -> ContextTransferFunc [Int] a)
  -> LabeledEdges
  -> [Int]
  -> M.Map Label a
  -> (LabeledEdges, [Int], M.Map Label a)
step _ _ []    ctx a = ([], ctx, a)
step flow transferFunctions edges ctx a =
  let (l, l', ty) = head edges
      w           = tail edges
      aL          = fromJust $ M.lookup l a
      aL'         = fromJust $ M.lookup l' a
      effect      = (transfer (transferFunctions l)) (\_ -> aL) ctx
  in case ty of
      Left () -> if not (effect <= aL')
                  then let successors = [ (l',l'',ty) | (l'',ty) <- lsuc flow l' ]
                           upA        = M.insert l' (aL' `join` effect) a
                       in (successors ++ w, ctx, upA)
                  else (w, ctx, a)
      Right I -> error "function transfer not supported"

-- generalize to scanl
-- scanl :: (b -> a -> b) -> b -> [a] -> [b]
-- scanl (step gr transfunc) initA 
-- return a function taking the edges and a
-- http://conal.net/blog/posts/deriving-list-scans/
