module Main where
import Test.HUnit
import JS.Test.Flow
import JS.Test.ConstantProp
import JS.Test.ConstantFold

main = 
  do
    runTestTT cfgTests
    runTestTT cpTests
    putStrLn "Folding test:"
    putStrLn "==============================="
    putStrLn "Test 1"
    putStrLn "==============================="
    putStrLn $ "input : " ++ testScript1
    putStrLn ""
    putStrLn "output:"
    putStr $ foldr (++) [] (foldTest (testScript1))
    putStrLn "==============================="
    putStrLn "Test 2"
    putStrLn "==============================="
    putStrLn $ "input : " ++ testScript2
    putStrLn ""
    putStrLn "output:"
    putStr $ foldr (++) [] (foldTest (testScript2))
    putStrLn "==============================="
    putStrLn "Test 3"
    putStrLn "==============================="
    putStrLn $ "input : " ++ testScript3
    putStrLn ""
    putStrLn "output:"
    putStr $ foldr (++) [] (foldTest (testScript3))

