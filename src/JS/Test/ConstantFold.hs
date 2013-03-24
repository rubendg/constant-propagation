module JS.Test.ConstantFold where
import JS.Analysis.ConstantPropagation
import JS.Analysis.CP.Base
import Components
import JS.AG as J
import Text.PrettyPrint.HughesPJ
import Monotone.Framework
import Data.Graph.Inductive.Graph as G

-- Represents the analyse data for a program
testScript1 = "x=5; y=6; z=x*y; r=z*2; g=3*r+1;"
testScript2 = "function f(){ x = 4; return x*2;} f();"
testScript3 = "x=3; y=5; if(x<y){z=10;}else{z=5;} g=2*z;"

-- Represents the constant propagation data
testAnalyseData :: String -> [(Int, [Int], String, ZTB)] 
testAnalyseData = (fst . cpFlatten . analysis . normalize . parseJS) 

-- executes a fold
fold :: String -> [(Int,[Int],String,ZTB)] -> [String]
fold script dat = (map showBlock . removeNonRelevant. optimise dat . getNodes . uptoControlFlow) script

-- executes a fold
foldTest :: String -> [String]
foldTest script = (fold script (testAnalyseData script))

showBlock :: Block -> String
showBlock (Skip l)           = show l ++ ": skip\n"
showBlock (Decl l v)         = show l ++ ": decl " ++ v ++ "\n"
showBlock (J.Call l1 l2 n p) = "entry: " ++ show l1 ++ " exit: " ++ show l2 ++ " call " ++ n ++ "(" ++ show p ++ ")\n"
showBlock (Assign l n e)     = show l ++ ": " ++ n ++ " = " ++ show e ++ "\n"
showBlock (J.Return l e)     = show l ++ ": return " ++ show e ++ "\n"
showBlock (While l e)        = show l ++ ": while(" ++ show e ++ ")\n"
showBlock (If l e)           = show l ++ ": if(" ++ show e ++ ")\n"
showBlock (Function l n p)   = show l ++ ": function " ++ n ++ "(" ++ show p ++ ")\n"
showBlock (End l)            = show l ++ ": end\n"
showBlock (ReturnFromCall l1 l2 n p r) = show l1 ++ ": returnfromcall " ++ n ++ "\n"               
                            
