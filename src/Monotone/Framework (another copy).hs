module Monotone.Framework (
   maximalFixedPoint
  ,computeMaximalFixedPoint
  ,fixedPointWithHistory
  ,mkFlowGraph
  ,flatten
  ,Lattice(..)
  ,ExtremalLabels
  ,ExtremalValue(..)
  ,TransferFunc(..)
  ,FlowGraph(intraFlow,interFlow)
  ,MonotoneFramework(..)
  ,Context(..)
  ,Effect(..)
  ,MFP(..)
  ,Label
) where
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Maybe (fromJust)

class Eq a => Lattice a where
  top     :: a
  bottom  :: a
  join    :: a -> a -> a
  meet    :: a -> a -> a

  (<:)    :: a -> a -> Bool
  x <: y = x `join` y == y  

data Lattice a => MonotoneFramework gr b c a = 
  MonotoneFramework { extremalLabels    :: ExtremalLabels
                    , extremalValues    :: ExtremalValue a
                    , transferFunctions :: Label -> TransferFunc a
                    , flowGraph         :: FlowGraph gr b c
                    }

type InterFlow = [(Int,Int,Int,Int)]

data G.Graph gr => FlowGraph gr a b = FlowGraph { intraFlow :: gr a b
                                                , interFlow :: InterFlow 
                                                }

data Lattice a => Context a = Context (M.Map Label a)
data Lattice a => Effect a  = Effect (M.Map Label a)

data Lattice a => MFP a = MFP { context :: Context a
                              , effect  :: Effect a
                              }

data Lattice a => TransferFunc a = TransferFunc { transfer :: a -> a }

data Lattice a => ContextTransferFunc c a = ContextTransferFunc { contextTransfer :: (c -> a) -> (c -> a) }

type ExtremalLabels = S.Set Label
data Lattice a => ExtremalValue a = ExtremalValue a

type Label = Int

flatten :: Lattice a => MFP a -> ([(Label,a)],[(Label,a)])
flatten mfp = let (Context c) = context mfp
                  (Effect e)  = effect mfp
              in (M.toList c, M.toList e)

mkFlowGraph :: G.Graph gr => gr a b -> InterFlow -> FlowGraph gr a b
mkFlowGraph intra inter = FlowGraph { intraFlow = intra, interFlow = inter }

computeMaximalFixedPoint :: (G.Graph gr, Lattice a) => MonotoneFramework gr b c a -> MFP a
computeMaximalFixedPoint = (flip maximalFixedPoint) fixedPoint

maximalFixedPoint :: (G.Graph gr, Lattice a) => 
     MonotoneFramework gr b c a 
  -> (gr b c -> (Label -> TransferFunc a) -> [(Int,Int)] -> M.Map Label a -> r) 
  -> r
maximalFixedPoint framework fixedPoint =
  let e                    = extremalLabels framework
      (ExtremalValue yota) = extremalValues framework
      tfFunc               = transferFunctions framework
      fg                   = flowGraph framework
      intraF               = intraFlow fg

      initA = let initialize l | l `S.member` e = (l, yota)
                               | otherwise      = (l, bottom)
              in M.fromList $ map initialize (G.nodes intraF)
          
  in fixedPoint intraF tfFunc (G.edges intraF) initA

fixedPoint flow transferFunctions w a = 
  let (w', a') = step flow transferFunctions w a
  in case w' of
      [] -> let effect = M.mapWithKey (\l v -> transfer (transferFunctions l) v) a' 
            in MFP (Context a') (Effect effect)
      _  -> fixedPoint flow transferFunctions w' a'

fixedPointWithHistory flow transferFunctions iw ia =
  [MFP (Context ia) (Effect ia)] ++ performIteration iw ia
  where
  performIteration w a = 
    let (w', a') = step flow transferFunctions w a
        effect   = M.mapWithKey (\l v -> transfer (transferFunctions l) v) a'
    in case w' of
        [] -> [MFP (Context a') (Effect effect)]
        _  -> [MFP (Context a') (Effect effect)] ++ (performIteration w' a')

step :: (G.Graph gr, Lattice a) => 
     gr b c
  -> (Label -> TransferFunc a)
  -> [(Int,Int)] 
  -> M.Map Label a 
  -> ([(Int,Int)],M.Map Label a)
step flow transferFunctions []    a = ([], a)
step flow transferFunctions edges a =
  let (l, l')   = head edges
      w         = tail edges
      aL        = fromJust $ M.lookup l a
      aL'       = fromJust $ M.lookup l' a
      effect    = transfer (transferFunctions l) aL
  in if not (effect <: aL')
      then let successors = [ (l',l'') | l'' <- G.suc flow l' ]
               upA        = M.insert l' (aL' `join` effect) a
           in (successors ++ w, upA)
      else (w, a)

-- generalize to scanl
-- scanl :: (b -> a -> b) -> b -> [a] -> [b]
-- scanl (step gr transfunc) initA 
-- return a function taking the edges and a
-- http://conal.net/blog/posts/deriving-list-scans/
