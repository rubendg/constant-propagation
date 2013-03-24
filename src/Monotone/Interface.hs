{-# LANGUAGE DatatypeContexts #-}
module Monotone.Interface where
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Graph.Inductive.Graph as G

-- Class for representing lattices
class Ord a => Lattice a where
  top     :: a
  bottom  :: a
  join    :: a -> a -> a
--  meet    :: a -> a -> a

type Label = Int
type From = Label
type To   = Label

type ProgramPoint = Label

type CallLabel   = Label
type EntryLabel  = Label
type ExitLabel   = Label
type ReturnLabel = Label

type InterFlowEntry = (CallLabel,EntryLabel,ExitLabel,ReturnLabel)
type InterFlow = [InterFlowEntry]

type FlowGraph gr n = (IntraFlow gr n, InterFlow)

-- Used for tagging interflow edges
data In = In
  deriving (Show, Ord, Eq)

-- Edges in the flow graph can either be of the type intraflow (unit)
-- or interflow (In). The algorithm, however, expects that only intraflow
-- edges are present. The possibility to store either inter or intra 
-- edges is merely there for visualization purposes. (this is a hack,
-- in an ideal situation the types should disallow flow graphs with
-- interprocedural edges to be passed to the algorithm.) 
type FlowEdgeLabel = Either () In

type FlowEdge = (From, To, FlowEdgeLabel)

-- | hide the type of the graph implementation since we don't care about it
type IntraFlow gr a = gr a FlowEdgeLabel

-- Transfer function types
type CtxInsUnaryTransfer l = l -> l
type CtxSenUnaryTransfer ctx l = (ctx -> l) -> ctx -> l
type CtxInsBinaryTransfer l = l -> l -> l
type CtxSenBinaryTransfer ctx l = (ctx -> l) -> (ctx -> l) -> ctx -> l

-- A transfer function can either be unary or binary
type TransferFunction ctx l = Either (CtxSenUnaryTransfer ctx l) (CtxSenBinaryTransfer ctx l)
-- A mapping between labels in the flow graph to their corresponding transfer function
type TransferFunctionSpace ctx l = ProgramPoint -> TransferFunction ctx l

-- A function that mutates the current context given a program point
type ContextMutator ctx = ProgramPoint -> ctx -> ctx
type ExtremalLabel = ProgramPoint

-- The analysis result (the primary output of the worklist algorithm) 
-- is represented by a mapping from program points to a lattice lifted to contexts.
type AnalysisResult ctx l = M.Map ProgramPoint (M.Map ctx l)

type Context ctx l = AnalysisResult ctx l
type Effect ctx l  = AnalysisResult ctx l

-- Each fixpoint iteration gives rise to a single result step.
data Step ctx l = Step (Context ctx l, Effect ctx l)

-- The maximal fixpoint is represented as the last step of the iteration
type MFP ctx l = Step ctx l

-- The embellished monotone framework
data (G.Graph gr, Ord ctx, Monoid ctx, Lattice l) => MonotoneFramework gr ctx node l =
  MF ( ExtremalLabel
     -- extremal value
     , l
     , TransferFunctionSpace ctx l
     , FlowGraph gr node
     , ContextMutator ctx
     )

-- | Lifts a unary transfer function to one that is context sensitive
liftUnary :: (Ord ctx, Lattice l) => CtxInsUnaryTransfer l -> CtxSenUnaryTransfer ctx l
liftUnary f l = f . l

-- | Lifts a binary transfer function to one that is context sensitive
liftBinary :: (Ord ctx, Lattice l) => CtxInsBinaryTransfer l -> CtxSenBinaryTransfer ctx l
liftBinary f l l' ctx = f (l ctx) (l' ctx)

flatten :: (Ord ctx, Lattice l) => MFP ctx l -> ([(Label,ctx,l)],[(Label,ctx,l)])
flatten (Step (c,e)) = (M.foldrWithKey f [] c, M.foldrWithKey f [] e)
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

