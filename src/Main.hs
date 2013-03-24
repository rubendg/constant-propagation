module Main where
import System.Environment ( getArgs )
import Data.Graph.Inductive.Graphviz
import Components

main :: IO ()
main = do
  args  <- getArgs
  input <- getContents
  case args of
    [] -> putStrLn usage
    xs -> case head xs of
            "cfg-intra" -> (printIntraCfg . uptoControlFlow) input

            "cfg-inter" -> (printInterCfg . uptoControlFlow) input

            "cfg-merged"   -> (printIntraCfg . mergeInterWithIntra . uptoControlFlow) input

            "cp"     -> putStrLn $ show (defaultPipeline input)

            "cp-l"   -> putStrLn $ show (defaultPipeline' input)

            "--help" -> putStrLn usage 

            otherwise -> do putStrLn ("Argument not recognized")
                            putStrLn usage

usage =
  "Reads a javascript program from stdin.\n\n" ++
  "Usage: [cfg|cp]?\n" ++
  "\tcfg-intra - prints the control flow graph (intra-procedural) in graphviz format\n" ++
  "\tcfg-inter - prints the inter-procedural flow\n" ++
  "\tcfg-merged - prints the inter and intra - procedural flow in graphviz format\n" ++
  "\tcp        - perform constant propagation analysis\n" ++
  "\tcp-l      - idem, but prints all intermediate steps\n\n" ++
  "Example: echo \"x=0;\" | ./cp cp"
  


