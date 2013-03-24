module Monotone.Framework (
   maximalFixedPoint
  ,mkFlowGraph
  ,Lattice(..)
  ,ExtremalLabels
  ,ExtremalValue(..)
  ,TransferFunc(..)
  ,FlowGraph(intraFlow,interFlow)
  ,MonotoneFramework(..)
  ,Context(..)
  ,Effect(..)
  ,MFP(..)
) where
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Data.Maybe (fromJust)

class Lattice a where
  top     :: a
  bottom  :: a
  join    :: a -> a -> a
  meet    :: a -> a -> a
  (<:)    :: a -> a -> Bool

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

data Context a = Context (M.Map Label a)
data Effect a  = Effect (M.Map Label a)

data Lattice a => MFP a = MFP { context :: Context a
                              , effect  :: Effect a
                              }

data Lattice a => TransferFunc a = TransferFunc { transfer :: a -> a }

type ExtremalLabels = S.Set Label
data Lattice a => ExtremalValue a = ExtremalValue a

type Label = Int

mkFlowGraph :: G.Graph gr => gr a b -> InterFlow -> FlowGraph gr a b
mkFlowGraph intra inter = FlowGraph { intraFlow = intra, interFlow = inter }

maximalFixedPoint :: (G.Graph gr, Lattice a) => MonotoneFramework gr b c a -> MFP a
maximalFixedPoint framework =
  let e                    = extremalLabels framework
      (ExtremalValue yota) = extremalValues framework
      tfFunc               = transferFunctions framework
      fg                   = flowGraph framework
      intraF               = intraFlow fg

      initA = let initialize l | l `S.member` e = (l, yota)
                               | otherwise      = (l, bottom)
              in M.fromList $ map initialize (G.nodes intraF)
          
      iterate []    a = ([], a)
      iterate edges a = 
        let (l, l')   = head edges
            w         = tail edges
            aL        = fromJust $ M.lookup l a
            aL'       = fromJust $ M.lookup l' a
            effect    = transfer (tfFunc l) aL
        in if effect <: aL'
            then let successors = [ (l',l'') | l'' <- G.suc intraF l' ]
                     upA        = M.insert l' (aL' `join` effect) a
                 in iterate (successors ++ w) upA
            else iterate w a
      
      -- perform iteration
      (_,ctx) = iterate (G.edges intraF) initA 

      effect  = M.mapWithKey (\l v -> transfer (tfFunc l) v) ctx
  in MFP (Context ctx) (Effect effect)

-- debug a w = a : iterate a w 

iterateWithContinuation :: Latttice a => [(Int,Int)] -> M.Map Label a -> ([(Int,Int)] -> M.Map Label a -> r) -> r

iterate []    a = ([], a)
iterate edges a = 
  let (l, l')   = head edges
      w         = tail edges
      aL        = fromJust $ M.lookup l a
      aL'       = fromJust $ M.lookup l' a
      effect    = transfer (tfFunc l) aL
  in if effect <: aL'
      then let successors = [ (l',l'') | l'' <- G.suc intraF l' ]
               upA        = M.insert l' (aL' `join` effect) a
           in iterate (successors ++ w) upA
      else iterate w a


