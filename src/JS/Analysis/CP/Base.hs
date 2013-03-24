{-# LANGUAGE StandaloneDeriving #-}
module JS.Analysis.CP.Base where
import Monotone.Interface
import qualified Data.Map as M

type Var = String

data ConstantProp = CP { lat :: M.Map Var ZTB }
  deriving (Eq)

data ZTB = Z Int
         | Top
         | Bottom
  deriving (Show, Eq)

type ConstantPropagationAnalysis = MFP [Int] ConstantProp


