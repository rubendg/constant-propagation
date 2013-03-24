module Components where
import Monotone.Framework
import Monotone.Interface
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import BrownPLT.JavaScript.Parser (parseScriptFromString)
import qualified BrownPLT.JavaScript.Syntax as B
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graphviz
import Text.ParserCombinators.Parsec (SourcePos)
import qualified JS.Normalize as N
import JS.AG
import JS.Analysis.ConstantPropagation
import JS.Analysis.CP.Base

defaultPipeline :: String -> ConstantPropagationAnalysis
defaultPipeline  = analysis . desugar . normalize . parseJS

defaultPipeline' = analysis' . desugar . normalize . parseJS

desugarPipeline = desugar . normalize . parseJS

-- gets the labelled nodes out of a Control flow diagram
getNodes :: G.Graph gr => JSControlFlow gr -> [Block]
getNodes (a, _) = map extract nodes
  where
  nodes = G.labNodes a
  extract (_,b) = b

-- Performs optimisation on javascript with constant-prop analysis data
optimise :: [(Int,[Int],String,ZTB)] -> Blocks -> Blocks
optimise e i =
  let wrap = wrap_Blocks (sem_Blocks i) (Inh_Blocks{ analyseData_Inh_Blocks = e })
  in folded_Syn_Blocks wrap

-- Filters out blocks that are not relevant for reconstruction to JS
removeNonRelevant :: Blocks -> Blocks
removeNonRelevant []     = []
removeNonRelevant (b:ls) = case b of
                             (Skip _)                   -> removeNonRelevant ls
                             (ReturnFromCall _ _ _ _ _) -> removeNonRelevant ls
                             _                          -> b : removeNonRelevant ls
                             
parseJS :: String -> B.JavaScript SourcePos
parseJS input = 
  case parseScriptFromString "" input of
    Left err -> error $ "parse error (" ++ show err ++ ")"
    Right x  -> x

normalize :: B.JavaScript SourcePos -> JavaScript
normalize = N.normalize . N.mapToSubset

controlFlow :: JavaScript -> (Int, FuncEnv, JSControlFlow Gr)
controlFlow js = 
  let wrap = wrap_JavaScript (sem_JavaScript js) Inh_JavaScript
  in ( extremalLabel_Syn_JavaScript wrap
     , env_Syn_JavaScript wrap
     , controlFlow_Syn_JavaScript wrap
     )

desugar :: JavaScript -> JavaScript
desugar js =
  let wrap = wrap_JavaScript (sem_JavaScript js) Inh_JavaScript
  in Script $ desugared_Syn_JavaScript wrap

uptoControlFlow :: String -> JSControlFlow Gr
uptoControlFlow = third  . controlFlow . desugar . normalize . parseJS

third = (\(_,_,x) -> x)

analysis :: JavaScript -> ConstantPropagationAnalysis
analysis js = 
  let avars                               = availableVars js
      (extremalLbl,funcEnv,(intra,inter)) = controlFlow js
      cfg                                 = mkFlowGraph intra inter
  in maximalFixedPoint (constantPropagation extremalLbl funcEnv avars cfg)

analysis' :: JavaScript -> [Step [Int] ConstantProp]
analysis' js = 
  let avars                               = availableVars js
      (extremalLbl,funcEnv,(intra,inter)) = controlFlow js
      cfg                                 = mkFlowGraph intra inter
  in maximalFixedPoint' (constantPropagation extremalLbl funcEnv avars cfg)

availableVars :: JavaScript -> (String -> AVars)
availableVars js s = 
  let wrap = wrap_JavaScript (sem_JavaScript js) (Inh_JavaScript)
  in case s of
      ""        -> vars_Syn_JavaScript wrap
      otherwise -> case M.lookup s (envAVars_Syn_JavaScript wrap) of
                    Nothing -> S.empty
                    Just x  -> x

printInterCfg :: (G.Graph gr, Show n) => FlowGraph gr n -> IO ()
printInterCfg = putStrLn . showInterCfg

printIntraCfg :: (G.Graph gr, Show n) => FlowGraph gr n -> IO ()
printIntraCfg = putStrLn . showIntraCfg

showInterCfg :: (G.Graph gr, Show n) => FlowGraph gr n -> String
showInterCfg (_,inter) = show inter

showIntraCfg :: (G.Graph gr, Show n) => FlowGraph gr n -> String
showIntraCfg (intra,_) = graphviz' intra  

mergeInterWithIntra :: G.DynGraph gr => JSControlFlow gr -> JSControlFlow gr
mergeInterWithIntra flow@(intra, inter) = 
  (foldr f intra inter, inter)
  where
  f (c,n,e,r) result = G.insEdge (c, n, Right In) (G.insEdge (e, r, Right In) result)

