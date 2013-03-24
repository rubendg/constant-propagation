

-- UUAGC 0.9.42.1 (src/JS/AG.ag)
module JS.AG where

{-# LINE 2 "./src/JS/AG/Flow.ag" #-}

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.PatriciaTree
import Text.ParserCombinators.Parsec
import Monotone.Interface
import Data.Either
import Data.Maybe
import Debug.Trace
import qualified Data.Map as M
{-# LINE 18 "src/JS/AG.hs" #-}

{-# LINE 2 "./src/JS/AG/Folding.ag" #-}

import JS.Analysis.CP.Base
import qualified Data.Graph.Inductive.Graph
{-# LINE 24 "src/JS/AG.hs" #-}

{-# LINE 2 "./src/JS/AG/AvailableVariables.ag" #-}

import qualified Data.Set as S
import qualified Data.Map as M
{-# LINE 30 "src/JS/AG.hs" #-}
{-# LINE 125 "./src/JS/AG/Base.ag" #-}



data ForInit = NoInit
             | VarInit VarDecls
             | ExprInit Expression
  deriving Show

data ExprValue = I Int | D Double | B Bool | S String | E Expression | N

data ExprType = TI | TD | TB | TS | TE | TN

deriving instance Show Block
deriving instance Show JavaScript
deriving instance Show Statement
deriving instance Show Expression
deriving instance Show MExpression
deriving instance Show LValue
deriving instance Show VarDecl
deriving instance Show AssignOp
deriving instance Show UnaryAssignOp
deriving instance Show PrefixOp
deriving instance Show InfixOp
deriving instance Show ExprType
deriving instance Show CaseClause
{-# LINE 57 "src/JS/AG.hs" #-}

{-# LINE 287 "./src/JS/AG/Flow.ag" #-}

type InternalFuncEnv = [(String,(Label, Label, [String]))]
type FuncEnv = M.Map String (Label, Label, [String])
type Labels = [Label]
type Result = String
  
type JSControlFlow gr = FlowGraph gr Block

infixr 1 |->
(|->) :: Label -> Label -> Either FlowEdge a
(|->) l l' = Left (l, l', Left ())

extremalLbl ((_,Function _ _ _) : xs) = extremalLbl (stripUntilEnd xs)
extremalLbl ((_,End _) : xs)          = extremalLbl xs
extremalLbl (x:_)                     = fst x
extremalLbl []                        = error "no extremal label"

stripUntilEnd xs = 
  let cond (_,End _) = False
      cond _         = True
  in dropWhile cond xs
{-# LINE 81 "src/JS/AG.hs" #-}

{-# LINE 238 "./src/JS/AG/Folding.ag" #-}
 
-- search a (string,label) combo in the environment that represents the constant propagation analysis data represented as (label,var-name,value)
searchEnv :: String -> Int -> [(Int,[Int],String,ZTB)] -> Maybe ZTB
searchEnv _ _ []                              = Nothing
searchEnv s i ((l,c,k,v):ls) | i == l && k == s = Just v
                             | otherwise        = searchEnv s i ls                         

-- determines the type of an expression value (Int, double, boolean, string, expression, null)
tyOf :: ExprValue -> ExprType
tyOf (I _) = TI
tyOf (D _) = TD
tyOf (B _) = TB
tyOf (S _) = TS
tyOf (E _) = TE
tyOf (N  ) = TN

-- extraction functions that extracts the real value of an expression out of an ExprValue wrapper
extractI :: ExprValue -> Int
extractI (I x) = x
extractI s     = error $ "extraction of Int not possible for type " ++ show (tyOf s)

extractD :: ExprValue -> Double
extractD (D x) = x
extractD s     = error $ "extraction of Double not possible for type " ++ show (tyOf s)

extractB :: ExprValue -> Bool
extractB (B x) = x
extractB s     = error $ "extraction of Bool not possible for type " ++ show (tyOf s)

extractS :: ExprValue -> String
extractS (S x) = x
extractS s     = error $ "extraction of String not possible for type " ++ show (tyOf s)
{-# LINE 116 "src/JS/AG.hs" #-}

{-# LINE 24 "./src/JS/AG/AvailableVariables.ag" #-}

type AVars = S.Set String
type EnvAVars = M.Map String AVars
{-# LINE 122 "src/JS/AG.hs" #-}

{-# LINE 67 "./src/JS/AG/Desugaring.ag" #-}

  
unbrokenStmts []                               = []
unbrokenStmts ((BreakStmt _) : _)              = []
unbrokenStmts ((BlockStmt stmts): ss)          = BlockStmt (unbrokenStmts stmts) : unbrokenStmts ss
unbrokenStmts ((IfStmt expr stmt1 stmt2) : ss) = IfStmt expr (BlockStmt (unbrokenStmts [stmt1])) (BlockStmt (unbrokenStmts [stmt2])) : unbrokenStmts ss
unbrokenStmts (s : ss)                         = s : unbrokenStmts ss

hasBreak [] = False
hasBreak ((BreakStmt _) : _) = True
hasBreak ((BlockStmt stmts) : ss)      = (hasBreak stmts) || hasBreak ss
hasBreak ((IfStmt _ stmt1 stmt2) : ss) = hasBreak [stmt1] || hasBreak [stmt2] || hasBreak ss
hasBreak (_:ss) = hasBreak ss

clauseExpr (CaseClause e _) = e
{-# LINE 140 "src/JS/AG.hs" #-}
-- AssignOp ----------------------------------------------------
data AssignOp = OpAssign
              | OpAssignAdd
              | OpAssignSub
              | OpAssignMul
              | OpAssignDiv
              | OpAssignMod
              | OpAssignLShift
              | OpAssignSpRShift
              | OpAssignZfRShift
              | OpAssignBAnd
              | OpAssignBXor
              | OpAssignBOr
-- cata
sem_AssignOp :: AssignOp ->
                T_AssignOp
sem_AssignOp (OpAssign) =
    (sem_AssignOp_OpAssign)
sem_AssignOp (OpAssignAdd) =
    (sem_AssignOp_OpAssignAdd)
sem_AssignOp (OpAssignSub) =
    (sem_AssignOp_OpAssignSub)
sem_AssignOp (OpAssignMul) =
    (sem_AssignOp_OpAssignMul)
sem_AssignOp (OpAssignDiv) =
    (sem_AssignOp_OpAssignDiv)
sem_AssignOp (OpAssignMod) =
    (sem_AssignOp_OpAssignMod)
sem_AssignOp (OpAssignLShift) =
    (sem_AssignOp_OpAssignLShift)
sem_AssignOp (OpAssignSpRShift) =
    (sem_AssignOp_OpAssignSpRShift)
sem_AssignOp (OpAssignZfRShift) =
    (sem_AssignOp_OpAssignZfRShift)
sem_AssignOp (OpAssignBAnd) =
    (sem_AssignOp_OpAssignBAnd)
sem_AssignOp (OpAssignBXor) =
    (sem_AssignOp_OpAssignBXor)
sem_AssignOp (OpAssignBOr) =
    (sem_AssignOp_OpAssignBOr)
-- semantic domain
type T_AssignOp = ( AssignOp)
data Inh_AssignOp = Inh_AssignOp {}
data Syn_AssignOp = Syn_AssignOp {self_Syn_AssignOp :: AssignOp}
wrap_AssignOp :: T_AssignOp ->
                 Inh_AssignOp ->
                 Syn_AssignOp
wrap_AssignOp sem (Inh_AssignOp) =
    (let ( _lhsOself) = sem
     in  (Syn_AssignOp _lhsOself))
sem_AssignOp_OpAssign :: T_AssignOp
sem_AssignOp_OpAssign =
    (let _lhsOself :: AssignOp
         _self =
             OpAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignAdd :: T_AssignOp
sem_AssignOp_OpAssignAdd =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignAdd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignSub :: T_AssignOp
sem_AssignOp_OpAssignSub =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignSub
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignMul :: T_AssignOp
sem_AssignOp_OpAssignMul =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignMul
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignDiv :: T_AssignOp
sem_AssignOp_OpAssignDiv =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignDiv
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignMod :: T_AssignOp
sem_AssignOp_OpAssignMod =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignMod
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignLShift :: T_AssignOp
sem_AssignOp_OpAssignLShift =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignLShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignSpRShift :: T_AssignOp
sem_AssignOp_OpAssignSpRShift =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignSpRShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignZfRShift :: T_AssignOp
sem_AssignOp_OpAssignZfRShift =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignZfRShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignBAnd :: T_AssignOp
sem_AssignOp_OpAssignBAnd =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignBAnd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignBXor :: T_AssignOp
sem_AssignOp_OpAssignBXor =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignBXor
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_AssignOp_OpAssignBOr :: T_AssignOp
sem_AssignOp_OpAssignBOr =
    (let _lhsOself :: AssignOp
         _self =
             OpAssignBOr
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Block -------------------------------------------------------
data Block = Skip (Label)
           | Decl (Label) (String)
           | Call (Label) (Label) (String) (Expressions)
           | Assign (Label) (String) (Expression)
           | Return (Label) (MExpression)
           | ReturnFromCall (Label) (Label) (String) (Expressions) (MResult)
           | While (Label) (Expression)
           | If (Label) (Expression)
           | Function (Label) (String) (([String]))
           | End (Label)
-- cata
sem_Block :: Block ->
             T_Block
sem_Block (Skip _lbl) =
    (sem_Block_Skip _lbl)
sem_Block (Decl _lbl _val) =
    (sem_Block_Decl _lbl _val)
sem_Block (Call _lbl1 _lbl2 _name _params) =
    (sem_Block_Call _lbl1 _lbl2 _name (sem_Expressions _params))
sem_Block (Assign _lbl _name _expr) =
    (sem_Block_Assign _lbl _name (sem_Expression _expr))
sem_Block (Return _lbl _expr) =
    (sem_Block_Return _lbl (sem_MExpression _expr))
sem_Block (ReturnFromCall _lbl1 _lbl2 _name _params _res) =
    (sem_Block_ReturnFromCall _lbl1 _lbl2 _name (sem_Expressions _params) (sem_MResult _res))
sem_Block (While _lbl _expr) =
    (sem_Block_While _lbl (sem_Expression _expr))
sem_Block (If _lbl _expr) =
    (sem_Block_If _lbl (sem_Expression _expr))
sem_Block (Function _lbl _name _params) =
    (sem_Block_Function _lbl _name _params)
sem_Block (End _lbl) =
    (sem_Block_End _lbl)
-- semantic domain
type T_Block = ([(Int,[Int],String,ZTB)]) ->
               ( Block,Block)
data Inh_Block = Inh_Block {analyseData_Inh_Block :: ([(Int,[Int],String,ZTB)])}
data Syn_Block = Syn_Block {folded_Syn_Block :: Block,self_Syn_Block :: Block}
wrap_Block :: T_Block ->
              Inh_Block ->
              Syn_Block
wrap_Block sem (Inh_Block _lhsIanalyseData) =
    (let ( _lhsOfolded,_lhsOself) = sem _lhsIanalyseData
     in  (Syn_Block _lhsOfolded _lhsOself))
sem_Block_Skip :: Label ->
                  T_Block
sem_Block_Skip lbl_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _lhsOself :: Block
              _lhsOfolded =
                  ({-# LINE 69 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 341 "src/JS/AG.hs" #-}
                   )
              _self =
                  Skip lbl_
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_Decl :: Label ->
                  String ->
                  T_Block
sem_Block_Decl lbl_ val_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _lhsOself :: Block
              _lhsOfolded =
                  ({-# LINE 71 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 358 "src/JS/AG.hs" #-}
                   )
              _self =
                  Decl lbl_ val_
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_Call :: Label ->
                  Label ->
                  String ->
                  T_Expressions ->
                  T_Block
sem_Block_Call lbl1_ lbl2_ name_ params_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _paramsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _paramsOcurrLabel :: Int
              _lhsOself :: Block
              _paramsOassignResultTo :: (Maybe String)
              _paramsOblocks :: (M.Map Label Block)
              _paramsOenv :: InternalFuncEnv
              _paramsOfinal :: (S.Set Label)
              _paramsOfresh :: Labels
              _paramsIblocks :: (M.Map Label Block)
              _paramsIenv :: InternalFuncEnv
              _paramsIenvAVars :: EnvAVars
              _paramsIfinal :: (S.Set Label)
              _paramsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _paramsIfolded :: Expressions
              _paramsIfresh :: Labels
              _paramsIinit :: (Maybe Label)
              _paramsIself :: Expressions
              _paramsIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 73 "./src/JS/AG/Folding.ag" #-}
                   Call lbl1_ lbl2_ name_ _paramsIfolded
                   {-# LINE 394 "src/JS/AG.hs" #-}
                   )
              _paramsOanalyseData =
                  ({-# LINE 74 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 399 "src/JS/AG.hs" #-}
                   )
              _paramsOcurrLabel =
                  ({-# LINE 75 "./src/JS/AG/Folding.ag" #-}
                   lbl1_
                   {-# LINE 404 "src/JS/AG.hs" #-}
                   )
              _self =
                  Call lbl1_ lbl2_ name_ _paramsIself
              _lhsOself =
                  _self
              _paramsOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Call.params.assignResultTo"
                   {-# LINE 413 "src/JS/AG.hs" #-}
                   )
              _paramsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Call.params.blocks"
                   {-# LINE 418 "src/JS/AG.hs" #-}
                   )
              _paramsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Call.params.env"
                   {-# LINE 423 "src/JS/AG.hs" #-}
                   )
              _paramsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Call.params.final"
                   {-# LINE 428 "src/JS/AG.hs" #-}
                   )
              _paramsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Call.params.fresh"
                   {-# LINE 433 "src/JS/AG.hs" #-}
                   )
              ( _paramsIblocks,_paramsIenv,_paramsIenvAVars,_paramsIfinal,_paramsIflow,_paramsIfolded,_paramsIfresh,_paramsIinit,_paramsIself,_paramsIvars) =
                  params_ _paramsOanalyseData _paramsOassignResultTo _paramsOblocks _paramsOcurrLabel _paramsOenv _paramsOfinal _paramsOfresh
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_Assign :: Label ->
                    String ->
                    T_Expression ->
                    T_Block
sem_Block_Assign lbl_ name_ expr_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _lhsOself :: Block
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 77 "./src/JS/AG/Folding.ag" #-}
                   Assign lbl_ name_ _exprIfolded
                   {-# LINE 467 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 78 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 472 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 79 "./src/JS/AG/Folding.ag" #-}
                   lbl_
                   {-# LINE 477 "src/JS/AG.hs" #-}
                   )
              _self =
                  Assign lbl_ name_ _exprIself
              _lhsOself =
                  _self
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Assign.expr.assignResultTo"
                   {-# LINE 486 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Assign.expr.blocks"
                   {-# LINE 491 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Assign.expr.env"
                   {-# LINE 496 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Assign.expr.final"
                   {-# LINE 501 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.Assign.expr.fresh"
                   {-# LINE 506 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_Return :: Label ->
                    T_MExpression ->
                    T_Block
sem_Block_Return lbl_ expr_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _lhsOself :: Block
              _exprIfolded :: MExpression
              _exprIself :: MExpression
              _lhsOfolded =
                  ({-# LINE 81 "./src/JS/AG/Folding.ag" #-}
                   Return lbl_ _exprIfolded
                   {-# LINE 525 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 82 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 530 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 83 "./src/JS/AG/Folding.ag" #-}
                   lbl_
                   {-# LINE 535 "src/JS/AG.hs" #-}
                   )
              _self =
                  Return lbl_ _exprIself
              _lhsOself =
                  _self
              ( _exprIfolded,_exprIself) =
                  expr_ _exprOanalyseData _exprOcurrLabel
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_ReturnFromCall :: Label ->
                            Label ->
                            String ->
                            T_Expressions ->
                            T_MResult ->
                            T_Block
sem_Block_ReturnFromCall lbl1_ lbl2_ name_ params_ res_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _paramsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _paramsOcurrLabel :: Int
              _lhsOself :: Block
              _paramsOassignResultTo :: (Maybe String)
              _paramsOblocks :: (M.Map Label Block)
              _paramsOenv :: InternalFuncEnv
              _paramsOfinal :: (S.Set Label)
              _paramsOfresh :: Labels
              _paramsIblocks :: (M.Map Label Block)
              _paramsIenv :: InternalFuncEnv
              _paramsIenvAVars :: EnvAVars
              _paramsIfinal :: (S.Set Label)
              _paramsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _paramsIfolded :: Expressions
              _paramsIfresh :: Labels
              _paramsIinit :: (Maybe Label)
              _paramsIself :: Expressions
              _paramsIvars :: AVars
              _resIself :: MResult
              _lhsOfolded =
                  ({-# LINE 85 "./src/JS/AG/Folding.ag" #-}
                   ReturnFromCall lbl1_ lbl2_ name_ _paramsIfolded _resIself
                   {-# LINE 575 "src/JS/AG.hs" #-}
                   )
              _paramsOanalyseData =
                  ({-# LINE 86 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 580 "src/JS/AG.hs" #-}
                   )
              _paramsOcurrLabel =
                  ({-# LINE 87 "./src/JS/AG/Folding.ag" #-}
                   lbl1_
                   {-# LINE 585 "src/JS/AG.hs" #-}
                   )
              _self =
                  ReturnFromCall lbl1_ lbl2_ name_ _paramsIself _resIself
              _lhsOself =
                  _self
              _paramsOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.ReturnFromCall.params.assignResultTo"
                   {-# LINE 594 "src/JS/AG.hs" #-}
                   )
              _paramsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.ReturnFromCall.params.blocks"
                   {-# LINE 599 "src/JS/AG.hs" #-}
                   )
              _paramsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.ReturnFromCall.params.env"
                   {-# LINE 604 "src/JS/AG.hs" #-}
                   )
              _paramsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.ReturnFromCall.params.final"
                   {-# LINE 609 "src/JS/AG.hs" #-}
                   )
              _paramsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.ReturnFromCall.params.fresh"
                   {-# LINE 614 "src/JS/AG.hs" #-}
                   )
              ( _paramsIblocks,_paramsIenv,_paramsIenvAVars,_paramsIfinal,_paramsIflow,_paramsIfolded,_paramsIfresh,_paramsIinit,_paramsIself,_paramsIvars) =
                  params_ _paramsOanalyseData _paramsOassignResultTo _paramsOblocks _paramsOcurrLabel _paramsOenv _paramsOfinal _paramsOfresh
              ( _resIself) =
                  res_
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_While :: Label ->
                   T_Expression ->
                   T_Block
sem_Block_While lbl_ expr_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _lhsOself :: Block
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 89 "./src/JS/AG/Folding.ag" #-}
                   While lbl_ _exprIfolded
                   {-# LINE 649 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 90 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 654 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 91 "./src/JS/AG/Folding.ag" #-}
                   lbl_
                   {-# LINE 659 "src/JS/AG.hs" #-}
                   )
              _self =
                  While lbl_ _exprIself
              _lhsOself =
                  _self
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.While.expr.assignResultTo"
                   {-# LINE 668 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.While.expr.blocks"
                   {-# LINE 673 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.While.expr.env"
                   {-# LINE 678 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.While.expr.final"
                   {-# LINE 683 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.While.expr.fresh"
                   {-# LINE 688 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_If :: Label ->
                T_Expression ->
                T_Block
sem_Block_If lbl_ expr_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _lhsOself :: Block
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 93 "./src/JS/AG/Folding.ag" #-}
                   If lbl_ _exprIfolded
                   {-# LINE 721 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 94 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 726 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 95 "./src/JS/AG/Folding.ag" #-}
                   lbl_
                   {-# LINE 731 "src/JS/AG.hs" #-}
                   )
              _self =
                  If lbl_ _exprIself
              _lhsOself =
                  _self
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.If.expr.assignResultTo"
                   {-# LINE 740 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.If.expr.blocks"
                   {-# LINE 745 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.If.expr.env"
                   {-# LINE 750 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.If.expr.final"
                   {-# LINE 755 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Block.If.expr.fresh"
                   {-# LINE 760 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_Function :: Label ->
                      String ->
                      ([String]) ->
                      T_Block
sem_Block_Function lbl_ name_ params_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _lhsOself :: Block
              _lhsOfolded =
                  ({-# LINE 97 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 776 "src/JS/AG.hs" #-}
                   )
              _self =
                  Function lbl_ name_ params_
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
sem_Block_End :: Label ->
                 T_Block
sem_Block_End lbl_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Block
              _lhsOself :: Block
              _lhsOfolded =
                  ({-# LINE 99 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 792 "src/JS/AG.hs" #-}
                   )
              _self =
                  End lbl_
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
-- Blocks ------------------------------------------------------
type Blocks = [Block]
-- cata
sem_Blocks :: Blocks ->
              T_Blocks
sem_Blocks list =
    (Prelude.foldr sem_Blocks_Cons sem_Blocks_Nil (Prelude.map sem_Block list))
-- semantic domain
type T_Blocks = ([(Int,[Int],String,ZTB)]) ->
                ( Blocks,Blocks)
data Inh_Blocks = Inh_Blocks {analyseData_Inh_Blocks :: ([(Int,[Int],String,ZTB)])}
data Syn_Blocks = Syn_Blocks {folded_Syn_Blocks :: Blocks,self_Syn_Blocks :: Blocks}
wrap_Blocks :: T_Blocks ->
               Inh_Blocks ->
               Syn_Blocks
wrap_Blocks sem (Inh_Blocks _lhsIanalyseData) =
    (let ( _lhsOfolded,_lhsOself) = sem _lhsIanalyseData
     in  (Syn_Blocks _lhsOfolded _lhsOself))
sem_Blocks_Cons :: T_Block ->
                   T_Blocks ->
                   T_Blocks
sem_Blocks_Cons hd_ tl_ =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Blocks
              _hdOanalyseData :: ([(Int,[Int],String,ZTB)])
              _tlOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOself :: Blocks
              _hdIfolded :: Block
              _hdIself :: Block
              _tlIfolded :: Blocks
              _tlIself :: Blocks
              _lhsOfolded =
                  ({-# LINE 40 "./src/JS/AG/Folding.ag" #-}
                   _hdIfolded : _tlIfolded
                   {-# LINE 833 "src/JS/AG.hs" #-}
                   )
              _hdOanalyseData =
                  ({-# LINE 41 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 838 "src/JS/AG.hs" #-}
                   )
              _tlOanalyseData =
                  ({-# LINE 42 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 843 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              ( _hdIfolded,_hdIself) =
                  hd_ _hdOanalyseData
              ( _tlIfolded,_tlIself) =
                  tl_ _tlOanalyseData
          in  ( _lhsOfolded,_lhsOself)))
sem_Blocks_Nil :: T_Blocks
sem_Blocks_Nil =
    (\ _lhsIanalyseData ->
         (let _lhsOfolded :: Blocks
              _lhsOself :: Blocks
              _lhsOfolded =
                  ({-# LINE 39 "./src/JS/AG/Folding.ag" #-}
                   []
                   {-# LINE 862 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
-- CaseClause --------------------------------------------------
data CaseClause = CaseClause (Expression) (Statements)
                | CaseDefault (Statements)
-- cata
sem_CaseClause :: CaseClause ->
                  T_CaseClause
sem_CaseClause (CaseClause _expr _stmts) =
    (sem_CaseClause_CaseClause (sem_Expression _expr) (sem_Statements _stmts))
sem_CaseClause (CaseDefault _stmts) =
    (sem_CaseClause_CaseDefault (sem_Statements _stmts))
-- semantic domain
type T_CaseClause = ( Statements,Bool,CaseClause,Statements)
data Inh_CaseClause = Inh_CaseClause {}
data Syn_CaseClause = Syn_CaseClause {desugared_Syn_CaseClause :: Statements,hasBreak_Syn_CaseClause :: Bool,self_Syn_CaseClause :: CaseClause,unbrokenStmts_Syn_CaseClause :: Statements}
wrap_CaseClause :: T_CaseClause ->
                   Inh_CaseClause ->
                   Syn_CaseClause
wrap_CaseClause sem (Inh_CaseClause) =
    (let ( _lhsOdesugared,_lhsOhasBreak,_lhsOself,_lhsOunbrokenStmts) = sem
     in  (Syn_CaseClause _lhsOdesugared _lhsOhasBreak _lhsOself _lhsOunbrokenStmts))
sem_CaseClause_CaseClause :: T_Expression ->
                             T_Statements ->
                             T_CaseClause
sem_CaseClause_CaseClause expr_ stmts_ =
    (let _lhsOdesugared :: Statements
         _lhsOunbrokenStmts :: Statements
         _lhsOhasBreak :: Bool
         _lhsOself :: CaseClause
         _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
         _exprOassignResultTo :: (Maybe String)
         _exprOblocks :: (M.Map Label Block)
         _exprOcurrLabel :: Int
         _exprOenv :: InternalFuncEnv
         _exprOfinal :: (S.Set Label)
         _exprOfresh :: Labels
         _stmtsOblocks :: (M.Map Label Block)
         _stmtsOenv :: InternalFuncEnv
         _stmtsOfinal :: (S.Set Label)
         _stmtsOfresh :: Labels
         _exprIblocks :: (M.Map Label Block)
         _exprIenv :: InternalFuncEnv
         _exprIenvAVars :: EnvAVars
         _exprIfinal :: (S.Set Label)
         _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
         _exprIfolded :: Expression
         _exprIfresh :: Labels
         _exprIinit :: (Maybe Label)
         _exprIself :: Expression
         _exprIvalue :: ExprValue
         _exprIvars :: AVars
         _stmtsIblocks :: (M.Map Label Block)
         _stmtsIdesugared :: Statements
         _stmtsIenv :: InternalFuncEnv
         _stmtsIenvAVars :: EnvAVars
         _stmtsIfinal :: (S.Set Label)
         _stmtsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
         _stmtsIfresh :: Labels
         _stmtsIinit :: (Maybe Label)
         _stmtsIself :: Statements
         _stmtsIvars :: AVars
         _lhsOdesugared =
             ({-# LINE 64 "./src/JS/AG/Desugaring.ag" #-}
              [BlockStmt _stmtsIdesugared]
              {-# LINE 932 "src/JS/AG.hs" #-}
              )
         _lhsOunbrokenStmts =
             ({-# LINE 65 "./src/JS/AG/Desugaring.ag" #-}
              unbrokenStmts _stmtsIdesugared
              {-# LINE 937 "src/JS/AG.hs" #-}
              )
         _lhsOhasBreak =
             ({-# LINE 66 "./src/JS/AG/Desugaring.ag" #-}
              hasBreak _stmtsIdesugared
              {-# LINE 942 "src/JS/AG.hs" #-}
              )
         _self =
             CaseClause _exprIself _stmtsIself
         _lhsOself =
             _self
         _exprOanalyseData =
             ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.analyseData"
              {-# LINE 951 "src/JS/AG.hs" #-}
              )
         _exprOassignResultTo =
             ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.assignResultTo"
              {-# LINE 956 "src/JS/AG.hs" #-}
              )
         _exprOblocks =
             ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.blocks"
              {-# LINE 961 "src/JS/AG.hs" #-}
              )
         _exprOcurrLabel =
             ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.currLabel"
              {-# LINE 966 "src/JS/AG.hs" #-}
              )
         _exprOenv =
             ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.env"
              {-# LINE 971 "src/JS/AG.hs" #-}
              )
         _exprOfinal =
             ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.final"
              {-# LINE 976 "src/JS/AG.hs" #-}
              )
         _exprOfresh =
             ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseClause.expr.fresh"
              {-# LINE 981 "src/JS/AG.hs" #-}
              )
         _stmtsOblocks =
             ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
              _exprIblocks
              {-# LINE 986 "src/JS/AG.hs" #-}
              )
         _stmtsOenv =
             ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
              _exprIenv
              {-# LINE 991 "src/JS/AG.hs" #-}
              )
         _stmtsOfinal =
             ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
              _exprIfinal
              {-# LINE 996 "src/JS/AG.hs" #-}
              )
         _stmtsOfresh =
             ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
              _exprIfresh
              {-# LINE 1001 "src/JS/AG.hs" #-}
              )
         ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
             expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
         ( _stmtsIblocks,_stmtsIdesugared,_stmtsIenv,_stmtsIenvAVars,_stmtsIfinal,_stmtsIflow,_stmtsIfresh,_stmtsIinit,_stmtsIself,_stmtsIvars) =
             stmts_ _stmtsOblocks _stmtsOenv _stmtsOfinal _stmtsOfresh
     in  ( _lhsOdesugared,_lhsOhasBreak,_lhsOself,_lhsOunbrokenStmts))
sem_CaseClause_CaseDefault :: T_Statements ->
                              T_CaseClause
sem_CaseClause_CaseDefault stmts_ =
    (let _lhsOdesugared :: Statements
         _lhsOunbrokenStmts :: Statements
         _lhsOhasBreak :: Bool
         _lhsOself :: CaseClause
         _stmtsOblocks :: (M.Map Label Block)
         _stmtsOenv :: InternalFuncEnv
         _stmtsOfinal :: (S.Set Label)
         _stmtsOfresh :: Labels
         _stmtsIblocks :: (M.Map Label Block)
         _stmtsIdesugared :: Statements
         _stmtsIenv :: InternalFuncEnv
         _stmtsIenvAVars :: EnvAVars
         _stmtsIfinal :: (S.Set Label)
         _stmtsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
         _stmtsIfresh :: Labels
         _stmtsIinit :: (Maybe Label)
         _stmtsIself :: Statements
         _stmtsIvars :: AVars
         _lhsOdesugared =
             ({-# LINE 64 "./src/JS/AG/Desugaring.ag" #-}
              [BlockStmt _stmtsIdesugared]
              {-# LINE 1032 "src/JS/AG.hs" #-}
              )
         _lhsOunbrokenStmts =
             ({-# LINE 65 "./src/JS/AG/Desugaring.ag" #-}
              unbrokenStmts _stmtsIdesugared
              {-# LINE 1037 "src/JS/AG.hs" #-}
              )
         _lhsOhasBreak =
             ({-# LINE 66 "./src/JS/AG/Desugaring.ag" #-}
              hasBreak _stmtsIdesugared
              {-# LINE 1042 "src/JS/AG.hs" #-}
              )
         _self =
             CaseDefault _stmtsIself
         _lhsOself =
             _self
         _stmtsOblocks =
             ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseDefault.stmts.blocks"
              {-# LINE 1051 "src/JS/AG.hs" #-}
              )
         _stmtsOenv =
             ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseDefault.stmts.env"
              {-# LINE 1056 "src/JS/AG.hs" #-}
              )
         _stmtsOfinal =
             ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseDefault.stmts.final"
              {-# LINE 1061 "src/JS/AG.hs" #-}
              )
         _stmtsOfresh =
             ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
              error "missing rule: CaseClause.CaseDefault.stmts.fresh"
              {-# LINE 1066 "src/JS/AG.hs" #-}
              )
         ( _stmtsIblocks,_stmtsIdesugared,_stmtsIenv,_stmtsIenvAVars,_stmtsIfinal,_stmtsIflow,_stmtsIfresh,_stmtsIinit,_stmtsIself,_stmtsIvars) =
             stmts_ _stmtsOblocks _stmtsOenv _stmtsOfinal _stmtsOfresh
     in  ( _lhsOdesugared,_lhsOhasBreak,_lhsOself,_lhsOunbrokenStmts))
-- CaseClauses -------------------------------------------------
type CaseClauses = [CaseClause]
-- cata
sem_CaseClauses :: CaseClauses ->
                   T_CaseClauses
sem_CaseClauses list =
    (Prelude.foldr sem_CaseClauses_Cons sem_CaseClauses_Nil (Prelude.map sem_CaseClause list))
-- semantic domain
type T_CaseClauses = Expression ->
                     ( Statements,Statements,CaseClauses)
data Inh_CaseClauses = Inh_CaseClauses {test_Inh_CaseClauses :: Expression}
data Syn_CaseClauses = Syn_CaseClauses {desugared_Syn_CaseClauses :: Statements,fallthrough_Syn_CaseClauses :: Statements,self_Syn_CaseClauses :: CaseClauses}
wrap_CaseClauses :: T_CaseClauses ->
                    Inh_CaseClauses ->
                    Syn_CaseClauses
wrap_CaseClauses sem (Inh_CaseClauses _lhsItest) =
    (let ( _lhsOdesugared,_lhsOfallthrough,_lhsOself) = sem _lhsItest
     in  (Syn_CaseClauses _lhsOdesugared _lhsOfallthrough _lhsOself))
sem_CaseClauses_Cons :: T_CaseClause ->
                        T_CaseClauses ->
                        T_CaseClauses
sem_CaseClauses_Cons hd_ tl_ =
    (\ _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOfallthrough :: Statements
              _lhsOself :: CaseClauses
              _tlOtest :: Expression
              _hdIdesugared :: Statements
              _hdIhasBreak :: Bool
              _hdIself :: CaseClause
              _hdIunbrokenStmts :: Statements
              _tlIdesugared :: Statements
              _tlIfallthrough :: Statements
              _tlIself :: CaseClauses
              _fallthrough =
                  ({-# LINE 49 "./src/JS/AG/Desugaring.ag" #-}
                   _hdIunbrokenStmts ++ if _hdIhasBreak
                                        then []
                                        else _tlIfallthrough
                   {-# LINE 1110 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 52 "./src/JS/AG/Desugaring.ag" #-}
                   case _hdIself of
                    CaseDefault _ -> [BlockStmt _hdIunbrokenStmts]
                    CaseClause test' _ -> [IfStmt (InfixExpr OpStrictEq
                                                             _lhsItest
                                                             (clauseExpr _hdIself))
                                                  (BlockStmt _fallthrough    )
                                                  (BlockStmt _tlIdesugared)]
                   {-# LINE 1121 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _fallthrough
                   {-# LINE 1126 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _tlOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 1135 "src/JS/AG.hs" #-}
                   )
              ( _hdIdesugared,_hdIhasBreak,_hdIself,_hdIunbrokenStmts) =
                  hd_
              ( _tlIdesugared,_tlIfallthrough,_tlIself) =
                  tl_ _tlOtest
          in  ( _lhsOdesugared,_lhsOfallthrough,_lhsOself)))
sem_CaseClauses_Nil :: T_CaseClauses
sem_CaseClauses_Nil =
    (\ _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOfallthrough :: Statements
              _lhsOself :: CaseClauses
              _lhsOdesugared =
                  ({-# LINE 5 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 1151 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 1156 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOdesugared,_lhsOfallthrough,_lhsOself)))
-- Expression --------------------------------------------------
data Expression = StringLit (String)
                | NumLit (Double)
                | IntLit (Int)
                | BoolLit (Bool)
                | NullLit
                | VarRef (String)
                | AssignExpr (String) (Expression)
                | ListExpr (Expressions)
                | CondExpr (Expression) (Expression) (Expression)
                | InfixExpr (InfixOp) (Expression) (Expression)
                | UnaryAssignExpr (UnaryAssignOp) (LValue)
                | PrefixExpr (PrefixOp) (Expression)
                | CallExpr (String) (Expressions)
                | ReturnFromCallExpr (String) (Expressions)
-- cata
sem_Expression :: Expression ->
                  T_Expression
sem_Expression (StringLit _val) =
    (sem_Expression_StringLit _val)
sem_Expression (NumLit _val) =
    (sem_Expression_NumLit _val)
sem_Expression (IntLit _val) =
    (sem_Expression_IntLit _val)
sem_Expression (BoolLit _val) =
    (sem_Expression_BoolLit _val)
sem_Expression (NullLit) =
    (sem_Expression_NullLit)
sem_Expression (VarRef _name) =
    (sem_Expression_VarRef _name)
sem_Expression (AssignExpr _l _r) =
    (sem_Expression_AssignExpr _l (sem_Expression _r))
sem_Expression (ListExpr _exprs) =
    (sem_Expression_ListExpr (sem_Expressions _exprs))
sem_Expression (CondExpr _expr1 _expr2 _expr3) =
    (sem_Expression_CondExpr (sem_Expression _expr1) (sem_Expression _expr2) (sem_Expression _expr3))
sem_Expression (InfixExpr _op _expr1 _expr2) =
    (sem_Expression_InfixExpr (sem_InfixOp _op) (sem_Expression _expr1) (sem_Expression _expr2))
sem_Expression (UnaryAssignExpr _op _val) =
    (sem_Expression_UnaryAssignExpr (sem_UnaryAssignOp _op) (sem_LValue _val))
sem_Expression (PrefixExpr _op _expr) =
    (sem_Expression_PrefixExpr (sem_PrefixOp _op) (sem_Expression _expr))
sem_Expression (CallExpr _name _params) =
    (sem_Expression_CallExpr _name (sem_Expressions _params))
sem_Expression (ReturnFromCallExpr _name _params) =
    (sem_Expression_ReturnFromCallExpr _name (sem_Expressions _params))
-- semantic domain
type T_Expression = ([(Int,[Int],String,ZTB)]) ->
                    (Maybe String) ->
                    (M.Map Label Block) ->
                    Int ->
                    InternalFuncEnv ->
                    (S.Set Label) ->
                    Labels ->
                    ( (M.Map Label Block),InternalFuncEnv,EnvAVars,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),Expression,Labels,(Maybe Label),Expression,ExprValue,AVars)
data Inh_Expression = Inh_Expression {analyseData_Inh_Expression :: ([(Int,[Int],String,ZTB)]),assignResultTo_Inh_Expression :: (Maybe String),blocks_Inh_Expression :: (M.Map Label Block),currLabel_Inh_Expression :: Int,env_Inh_Expression :: InternalFuncEnv,final_Inh_Expression :: (S.Set Label),fresh_Inh_Expression :: Labels}
data Syn_Expression = Syn_Expression {blocks_Syn_Expression :: (M.Map Label Block),env_Syn_Expression :: InternalFuncEnv,envAVars_Syn_Expression :: EnvAVars,final_Syn_Expression :: (S.Set Label),flow_Syn_Expression :: (S.Set (Either FlowEdge InterFlowEntry)),folded_Syn_Expression :: Expression,fresh_Syn_Expression :: Labels,init_Syn_Expression :: (Maybe Label),self_Syn_Expression :: Expression,value_Syn_Expression :: ExprValue,vars_Syn_Expression :: AVars}
wrap_Expression :: T_Expression ->
                   Inh_Expression ->
                   Syn_Expression
wrap_Expression sem (Inh_Expression _lhsIanalyseData _lhsIassignResultTo _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh) =
    (let ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars) = sem _lhsIanalyseData _lhsIassignResultTo _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh
     in  (Syn_Expression _lhsOblocks _lhsOenv _lhsOenvAVars _lhsOfinal _lhsOflow _lhsOfolded _lhsOfresh _lhsOinit _lhsOself _lhsOvalue _lhsOvars))
sem_Expression_StringLit :: String ->
                            T_Expression
sem_Expression_StringLit val_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 102 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 1250 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 103 "./src/JS/AG/Folding.ag" #-}
                   S val_
                   {-# LINE 1255 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 104 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1260 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1265 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1270 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1275 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1280 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 1285 "src/JS/AG.hs" #-}
                   )
              _self =
                  StringLit val_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1294 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1299 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.StringLit.lhs.init"
                   {-# LINE 1304 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_NumLit :: Double ->
                         T_Expression
sem_Expression_NumLit val_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 106 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 1331 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 107 "./src/JS/AG/Folding.ag" #-}
                   D val_
                   {-# LINE 1336 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 108 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1341 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1346 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1351 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1356 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1361 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 1366 "src/JS/AG.hs" #-}
                   )
              _self =
                  NumLit val_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1375 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1380 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.NumLit.lhs.init"
                   {-# LINE 1385 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_IntLit :: Int ->
                         T_Expression
sem_Expression_IntLit val_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 110 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 1412 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 111 "./src/JS/AG/Folding.ag" #-}
                   I val_
                   {-# LINE 1417 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 112 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1422 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1427 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1432 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1437 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1442 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 1447 "src/JS/AG.hs" #-}
                   )
              _self =
                  IntLit val_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1456 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1461 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.IntLit.lhs.init"
                   {-# LINE 1466 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_BoolLit :: Bool ->
                          T_Expression
sem_Expression_BoolLit val_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 114 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 1493 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 115 "./src/JS/AG/Folding.ag" #-}
                   B val_
                   {-# LINE 1498 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 116 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1503 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1508 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1513 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1518 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1523 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 1528 "src/JS/AG.hs" #-}
                   )
              _self =
                  BoolLit val_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1537 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1542 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.BoolLit.lhs.init"
                   {-# LINE 1547 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_NullLit :: T_Expression
sem_Expression_NullLit =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 118 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 1573 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 119 "./src/JS/AG/Folding.ag" #-}
                   N
                   {-# LINE 1578 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 120 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1583 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1588 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1593 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1598 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1603 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 1608 "src/JS/AG.hs" #-}
                   )
              _self =
                  NullLit
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1617 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1622 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.NullLit.lhs.init"
                   {-# LINE 1627 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_VarRef :: String ->
                         T_Expression
sem_Expression_VarRef name_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOvars :: AVars
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lhsOfolded =
                  ({-# LINE 122 "./src/JS/AG/Folding.ag" #-}
                   case _value     of
                     (S n) -> _self
                     (I x) -> IntLit x
                   {-# LINE 1656 "src/JS/AG.hs" #-}
                   )
              _value =
                  ({-# LINE 127 "./src/JS/AG/Folding.ag" #-}
                   case searchEnv name_ _lhsIcurrLabel _lhsIanalyseData of
                         Just v ->  case v of
                                      Bottom -> error $ "use of uninitialised variable " ++ name_ ++ " (stmt-label: " ++ show _lhsIcurrLabel ++ ")"
                                      Top    -> S name_
                                      Z x    -> I x
                         Nothing -> S name_
                   {-# LINE 1666 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 134 "./src/JS/AG/Folding.ag" #-}
                   _value
                   {-# LINE 1671 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 135 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1676 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 20 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.singleton name_
                   {-# LINE 1681 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 1686 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 1691 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1696 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 1701 "src/JS/AG.hs" #-}
                   )
              _self =
                  VarRef name_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1710 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1715 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.VarRef.lhs.init"
                   {-# LINE 1720 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_AssignExpr :: String ->
                             T_Expression ->
                             T_Expression
sem_Expression_AssignExpr l_ r_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _rOassignResultTo :: (Maybe String)
              _lhsOfolded :: Expression
              _rOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOvars :: AVars
              _lhsOenvAVars :: EnvAVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _rOblocks :: (M.Map Label Block)
              _rOcurrLabel :: Int
              _rOenv :: InternalFuncEnv
              _rOfinal :: (S.Set Label)
              _rOfresh :: Labels
              _rIblocks :: (M.Map Label Block)
              _rIenv :: InternalFuncEnv
              _rIenvAVars :: EnvAVars
              _rIfinal :: (S.Set Label)
              _rIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _rIfolded :: Expression
              _rIfresh :: Labels
              _rIinit :: (Maybe Label)
              _rIself :: Expression
              _rIvalue :: ExprValue
              _rIvars :: AVars
              _lbl =
                  ({-# LINE 220 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 1766 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 222 "./src/JS/AG/Flow.ag" #-}
                   case M.null _rIblocks of
                     True  -> Just _lbl
                     False -> _rIinit
                   {-# LINE 1773 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 227 "./src/JS/AG/Flow.ag" #-}
                   case M.null _rIblocks of
                     True  -> S.singleton _lbl
                     False -> _rIfinal
                   {-# LINE 1780 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 232 "./src/JS/AG/Flow.ag" #-}
                   case M.null _rIblocks of
                     True  -> M.singleton _lbl     (Assign _lbl     l_ _rIself)
                     False -> _rIblocks
                   {-# LINE 1787 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 237 "./src/JS/AG/Flow.ag" #-}
                   case M.null _rIblocks of
                     True  -> S.empty
                     False -> _rIflow
                   {-# LINE 1794 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 242 "./src/JS/AG/Flow.ag" #-}
                   case M.null _rIblocks of
                     True  -> tail _lhsIfresh
                     False -> _rIfresh
                   {-# LINE 1801 "src/JS/AG.hs" #-}
                   )
              _rOassignResultTo =
                  ({-# LINE 247 "./src/JS/AG/Flow.ag" #-}
                   Just l_
                   {-# LINE 1806 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 137 "./src/JS/AG/Folding.ag" #-}
                   AssignExpr l_ _rIfolded
                   {-# LINE 1811 "src/JS/AG.hs" #-}
                   )
              _rOanalyseData =
                  ({-# LINE 138 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1816 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 139 "./src/JS/AG/Folding.ag" #-}
                   E $ AssignExpr l_ _rIfolded
                   {-# LINE 1821 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 21 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.insert l_ _rIvars
                   {-# LINE 1826 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _rIenvAVars
                   {-# LINE 1831 "src/JS/AG.hs" #-}
                   )
              _self =
                  AssignExpr l_ _rIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _rIenv
                   {-# LINE 1840 "src/JS/AG.hs" #-}
                   )
              _rOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 1845 "src/JS/AG.hs" #-}
                   )
              _rOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 1850 "src/JS/AG.hs" #-}
                   )
              _rOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1855 "src/JS/AG.hs" #-}
                   )
              _rOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 1860 "src/JS/AG.hs" #-}
                   )
              _rOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1865 "src/JS/AG.hs" #-}
                   )
              ( _rIblocks,_rIenv,_rIenvAVars,_rIfinal,_rIflow,_rIfolded,_rIfresh,_rIinit,_rIself,_rIvalue,_rIvars) =
                  r_ _rOanalyseData _rOassignResultTo _rOblocks _rOcurrLabel _rOenv _rOfinal _rOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_ListExpr :: T_Expressions ->
                           T_Expression
sem_Expression_ListExpr exprs_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _exprsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _exprsOassignResultTo :: (Maybe String)
              _exprsOblocks :: (M.Map Label Block)
              _exprsOcurrLabel :: Int
              _exprsOenv :: InternalFuncEnv
              _exprsOfinal :: (S.Set Label)
              _exprsOfresh :: Labels
              _exprsIblocks :: (M.Map Label Block)
              _exprsIenv :: InternalFuncEnv
              _exprsIenvAVars :: EnvAVars
              _exprsIfinal :: (S.Set Label)
              _exprsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprsIfolded :: Expressions
              _exprsIfresh :: Labels
              _exprsIinit :: (Maybe Label)
              _exprsIself :: Expressions
              _exprsIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 141 "./src/JS/AG/Folding.ag" #-}
                   ListExpr _exprsIfolded
                   {-# LINE 1911 "src/JS/AG.hs" #-}
                   )
              _exprsOanalyseData =
                  ({-# LINE 142 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 1916 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 143 "./src/JS/AG/Folding.ag" #-}
                   E $ ListExpr _exprsIfolded
                   {-# LINE 1921 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _exprsIblocks
                   {-# LINE 1926 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprsIenvAVars
                   {-# LINE 1931 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _exprsIfinal
                   {-# LINE 1936 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _exprsIflow
                   {-# LINE 1941 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprsIvars
                   {-# LINE 1946 "src/JS/AG.hs" #-}
                   )
              _self =
                  ListExpr _exprsIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprsIenv
                   {-# LINE 1955 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _exprsIfresh
                   {-# LINE 1960 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _exprsIinit
                   {-# LINE 1965 "src/JS/AG.hs" #-}
                   )
              _exprsOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 1970 "src/JS/AG.hs" #-}
                   )
              _exprsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 1975 "src/JS/AG.hs" #-}
                   )
              _exprsOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 1980 "src/JS/AG.hs" #-}
                   )
              _exprsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 1985 "src/JS/AG.hs" #-}
                   )
              _exprsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 1990 "src/JS/AG.hs" #-}
                   )
              _exprsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 1995 "src/JS/AG.hs" #-}
                   )
              ( _exprsIblocks,_exprsIenv,_exprsIenvAVars,_exprsIfinal,_exprsIflow,_exprsIfolded,_exprsIfresh,_exprsIinit,_exprsIself,_exprsIvars) =
                  exprs_ _exprsOanalyseData _exprsOassignResultTo _exprsOblocks _exprsOcurrLabel _exprsOenv _exprsOfinal _exprsOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_CondExpr :: T_Expression ->
                           T_Expression ->
                           T_Expression ->
                           T_Expression
sem_Expression_CondExpr expr1_ expr2_ expr3_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _expr1OanalyseData :: ([(Int,[Int],String,ZTB)])
              _expr2OanalyseData :: ([(Int,[Int],String,ZTB)])
              _expr3OanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _expr1OassignResultTo :: (Maybe String)
              _expr1Oblocks :: (M.Map Label Block)
              _expr1OcurrLabel :: Int
              _expr1Oenv :: InternalFuncEnv
              _expr1Ofinal :: (S.Set Label)
              _expr1Ofresh :: Labels
              _expr2OassignResultTo :: (Maybe String)
              _expr2Oblocks :: (M.Map Label Block)
              _expr2OcurrLabel :: Int
              _expr2Oenv :: InternalFuncEnv
              _expr2Ofinal :: (S.Set Label)
              _expr2Ofresh :: Labels
              _expr3OassignResultTo :: (Maybe String)
              _expr3Oblocks :: (M.Map Label Block)
              _expr3OcurrLabel :: Int
              _expr3Oenv :: InternalFuncEnv
              _expr3Ofinal :: (S.Set Label)
              _expr3Ofresh :: Labels
              _expr1Iblocks :: (M.Map Label Block)
              _expr1Ienv :: InternalFuncEnv
              _expr1IenvAVars :: EnvAVars
              _expr1Ifinal :: (S.Set Label)
              _expr1Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _expr1Ifolded :: Expression
              _expr1Ifresh :: Labels
              _expr1Iinit :: (Maybe Label)
              _expr1Iself :: Expression
              _expr1Ivalue :: ExprValue
              _expr1Ivars :: AVars
              _expr2Iblocks :: (M.Map Label Block)
              _expr2Ienv :: InternalFuncEnv
              _expr2IenvAVars :: EnvAVars
              _expr2Ifinal :: (S.Set Label)
              _expr2Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _expr2Ifolded :: Expression
              _expr2Ifresh :: Labels
              _expr2Iinit :: (Maybe Label)
              _expr2Iself :: Expression
              _expr2Ivalue :: ExprValue
              _expr2Ivars :: AVars
              _expr3Iblocks :: (M.Map Label Block)
              _expr3Ienv :: InternalFuncEnv
              _expr3IenvAVars :: EnvAVars
              _expr3Ifinal :: (S.Set Label)
              _expr3Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _expr3Ifolded :: Expression
              _expr3Ifresh :: Labels
              _expr3Iinit :: (Maybe Label)
              _expr3Iself :: Expression
              _expr3Ivalue :: ExprValue
              _expr3Ivars :: AVars
              _lhsOfolded =
                  ({-# LINE 145 "./src/JS/AG/Folding.ag" #-}
                   CondExpr _expr1Ifolded _expr2Ifolded _expr3Ifolded
                   {-# LINE 2080 "src/JS/AG.hs" #-}
                   )
              _expr1OanalyseData =
                  ({-# LINE 146 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2085 "src/JS/AG.hs" #-}
                   )
              _expr2OanalyseData =
                  ({-# LINE 147 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2090 "src/JS/AG.hs" #-}
                   )
              _expr3OanalyseData =
                  ({-# LINE 148 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2095 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 149 "./src/JS/AG/Folding.ag" #-}
                   E $ CondExpr _expr1Ifolded _expr2Ifolded _expr3Ifolded
                   {-# LINE 2100 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iblocks `M.union` _expr2Iblocks `M.union` _expr3Iblocks
                   {-# LINE 2105 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _expr1IenvAVars `M.union` _expr2IenvAVars `M.union` _expr3IenvAVars
                   {-# LINE 2110 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifinal `S.union` _expr2Ifinal `S.union` _expr3Ifinal
                   {-# LINE 2115 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iflow `S.union` _expr2Iflow `S.union` _expr3Iflow
                   {-# LINE 2120 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _expr1Ivars `S.union` _expr2Ivars `S.union` _expr3Ivars
                   {-# LINE 2125 "src/JS/AG.hs" #-}
                   )
              _self =
                  CondExpr _expr1Iself _expr2Iself _expr3Iself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _expr3Ienv
                   {-# LINE 2134 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _expr3Ifresh
                   {-# LINE 2139 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _expr3Iinit
                   {-# LINE 2144 "src/JS/AG.hs" #-}
                   )
              _expr1OassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2149 "src/JS/AG.hs" #-}
                   )
              _expr1Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 2154 "src/JS/AG.hs" #-}
                   )
              _expr1OcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2159 "src/JS/AG.hs" #-}
                   )
              _expr1Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2164 "src/JS/AG.hs" #-}
                   )
              _expr1Ofinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 2169 "src/JS/AG.hs" #-}
                   )
              _expr1Ofresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2174 "src/JS/AG.hs" #-}
                   )
              _expr2OassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2179 "src/JS/AG.hs" #-}
                   )
              _expr2Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iblocks
                   {-# LINE 2184 "src/JS/AG.hs" #-}
                   )
              _expr2OcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2189 "src/JS/AG.hs" #-}
                   )
              _expr2Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ienv
                   {-# LINE 2194 "src/JS/AG.hs" #-}
                   )
              _expr2Ofinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifinal
                   {-# LINE 2199 "src/JS/AG.hs" #-}
                   )
              _expr2Ofresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifresh
                   {-# LINE 2204 "src/JS/AG.hs" #-}
                   )
              _expr3OassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2209 "src/JS/AG.hs" #-}
                   )
              _expr3Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _expr2Iblocks
                   {-# LINE 2214 "src/JS/AG.hs" #-}
                   )
              _expr3OcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2219 "src/JS/AG.hs" #-}
                   )
              _expr3Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _expr2Ienv
                   {-# LINE 2224 "src/JS/AG.hs" #-}
                   )
              _expr3Ofinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _expr2Ifinal
                   {-# LINE 2229 "src/JS/AG.hs" #-}
                   )
              _expr3Ofresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _expr2Ifresh
                   {-# LINE 2234 "src/JS/AG.hs" #-}
                   )
              ( _expr1Iblocks,_expr1Ienv,_expr1IenvAVars,_expr1Ifinal,_expr1Iflow,_expr1Ifolded,_expr1Ifresh,_expr1Iinit,_expr1Iself,_expr1Ivalue,_expr1Ivars) =
                  expr1_ _expr1OanalyseData _expr1OassignResultTo _expr1Oblocks _expr1OcurrLabel _expr1Oenv _expr1Ofinal _expr1Ofresh
              ( _expr2Iblocks,_expr2Ienv,_expr2IenvAVars,_expr2Ifinal,_expr2Iflow,_expr2Ifolded,_expr2Ifresh,_expr2Iinit,_expr2Iself,_expr2Ivalue,_expr2Ivars) =
                  expr2_ _expr2OanalyseData _expr2OassignResultTo _expr2Oblocks _expr2OcurrLabel _expr2Oenv _expr2Ofinal _expr2Ofresh
              ( _expr3Iblocks,_expr3Ienv,_expr3IenvAVars,_expr3Ifinal,_expr3Iflow,_expr3Ifolded,_expr3Ifresh,_expr3Iinit,_expr3Iself,_expr3Ivalue,_expr3Ivars) =
                  expr3_ _expr3OanalyseData _expr3OassignResultTo _expr3Oblocks _expr3OcurrLabel _expr3Oenv _expr3Ofinal _expr3Ofresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_InfixExpr :: T_InfixOp ->
                            T_Expression ->
                            T_Expression ->
                            T_Expression
sem_Expression_InfixExpr op_ expr1_ expr2_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _expr1OanalyseData :: ([(Int,[Int],String,ZTB)])
              _expr2OanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _expr1OassignResultTo :: (Maybe String)
              _expr1Oblocks :: (M.Map Label Block)
              _expr1OcurrLabel :: Int
              _expr1Oenv :: InternalFuncEnv
              _expr1Ofinal :: (S.Set Label)
              _expr1Ofresh :: Labels
              _expr2OassignResultTo :: (Maybe String)
              _expr2Oblocks :: (M.Map Label Block)
              _expr2OcurrLabel :: Int
              _expr2Oenv :: InternalFuncEnv
              _expr2Ofinal :: (S.Set Label)
              _expr2Ofresh :: Labels
              _opIself :: InfixOp
              _expr1Iblocks :: (M.Map Label Block)
              _expr1Ienv :: InternalFuncEnv
              _expr1IenvAVars :: EnvAVars
              _expr1Ifinal :: (S.Set Label)
              _expr1Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _expr1Ifolded :: Expression
              _expr1Ifresh :: Labels
              _expr1Iinit :: (Maybe Label)
              _expr1Iself :: Expression
              _expr1Ivalue :: ExprValue
              _expr1Ivars :: AVars
              _expr2Iblocks :: (M.Map Label Block)
              _expr2Ienv :: InternalFuncEnv
              _expr2IenvAVars :: EnvAVars
              _expr2Ifinal :: (S.Set Label)
              _expr2Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _expr2Ifolded :: Expression
              _expr2Ifresh :: Labels
              _expr2Iinit :: (Maybe Label)
              _expr2Iself :: Expression
              _expr2Ivalue :: ExprValue
              _expr2Ivars :: AVars
              _lhsOfolded =
                  ({-# LINE 151 "./src/JS/AG/Folding.ag" #-}
                   case _value     of
                     (I x) -> IntLit x
                     (D x) -> NumLit x
                     (B x) -> BoolLit x
                     (S x) -> StringLit x
                     (E x) -> x
                   {-# LINE 2311 "src/JS/AG.hs" #-}
                   )
              _expr1OanalyseData =
                  ({-# LINE 158 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2316 "src/JS/AG.hs" #-}
                   )
              _expr2OanalyseData =
                  ({-# LINE 159 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2321 "src/JS/AG.hs" #-}
                   )
              _value =
                  ({-# LINE 161 "./src/JS/AG/Folding.ag" #-}
                   case (tyOf _expr1Ivalue,tyOf _expr2Ivalue) of
                   (TI,TI) -> case _opIself of
                                OpAdd -> I $ (extractI _expr1Ivalue) + (extractI _expr2Ivalue)
                                OpMul -> I $ (extractI _expr1Ivalue) * (extractI _expr2Ivalue)
                                OpSub -> I $ (extractI _expr1Ivalue) - (extractI _expr2Ivalue)
                                OpLT  -> B $ (extractI _expr1Ivalue) < (extractI _expr2Ivalue)
                                OpLEq -> B $ (extractI _expr1Ivalue) <= (extractI _expr2Ivalue)
                                OpGT  -> B $ (extractI _expr1Ivalue) > (extractI _expr2Ivalue)
                                OpGEq -> B $ (extractI _expr1Ivalue) >= (extractI _expr2Ivalue)
                                OpEq  -> B $ (extractI _expr1Ivalue) == (extractI _expr2Ivalue)
                                OpNEq -> B $ not $ (extractI _expr1Ivalue) == (extractI _expr2Ivalue)
                                _     -> error "not yet supported"
                   (TD,TD) -> case _opIself of
                                OpAdd -> D $ (extractD _expr1Ivalue) + (extractD _expr2Ivalue)
                                OpMul -> D $ (extractD _expr1Ivalue) * (extractD _expr2Ivalue)
                                OpSub -> D $ (extractD _expr1Ivalue) - (extractD _expr2Ivalue)
                                OpDiv -> D $ (extractD _expr1Ivalue) / (extractD _expr2Ivalue)
                                OpLT  -> B $ (extractD _expr1Ivalue) < (extractD _expr2Ivalue)
                                OpLEq -> B $ (extractD _expr1Ivalue) <= (extractD _expr2Ivalue)
                                OpGT  -> B $ (extractD _expr1Ivalue) > (extractD _expr2Ivalue)
                                OpGEq -> B $ (extractD _expr1Ivalue) >= (extractD _expr2Ivalue)
                                OpEq  -> B $ (extractD _expr1Ivalue) == (extractD _expr2Ivalue)
                                OpNEq -> B $ not $ (extractD _expr1Ivalue) == (extractD _expr2Ivalue)
                                _     -> error "not yet supported"
                   (TB,TB) -> case _opIself of
                                OpLT  -> B $ (extractB _expr1Ivalue) < (extractB _expr2Ivalue)
                                OpLEq -> B $ (extractB _expr1Ivalue) <= (extractB _expr2Ivalue)
                                OpGT  -> B $ (extractB _expr1Ivalue) > (extractB _expr2Ivalue)
                                OpGEq -> B $ (extractB _expr1Ivalue) >= (extractB _expr2Ivalue)
                                OpEq  -> B $ (extractB _expr1Ivalue) == (extractB _expr2Ivalue)
                                OpNEq -> B $ not $ (extractB _expr1Ivalue) == (extractB _expr2Ivalue)
                                _     -> error "not yet supported"
                   (TS,TS) -> case _opIself of
                                OpLT  -> B $ (extractS _expr1Ivalue) < (extractS _expr2Ivalue)
                                OpLEq -> B $ (extractS _expr1Ivalue) <= (extractS _expr2Ivalue)
                                OpGT  -> B $ (extractS _expr1Ivalue) > (extractS _expr2Ivalue)
                                OpGEq -> B $ (extractS _expr1Ivalue) >= (extractS _expr2Ivalue)
                                OpEq  -> B $ (extractS _expr1Ivalue) == (extractS _expr2Ivalue)
                                OpNEq -> B $ not $ (extractS _expr1Ivalue) == (extractS _expr2Ivalue)
                                _     -> error "not yet supported"
                   (_,_)   -> E _self
                   {-# LINE 2366 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 208 "./src/JS/AG/Folding.ag" #-}
                   _value
                   {-# LINE 2371 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iblocks `M.union` _expr2Iblocks
                   {-# LINE 2376 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _expr1IenvAVars `M.union` _expr2IenvAVars
                   {-# LINE 2381 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifinal `S.union` _expr2Ifinal
                   {-# LINE 2386 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iflow `S.union` _expr2Iflow
                   {-# LINE 2391 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _expr1Ivars `S.union` _expr2Ivars
                   {-# LINE 2396 "src/JS/AG.hs" #-}
                   )
              _self =
                  InfixExpr _opIself _expr1Iself _expr2Iself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _expr2Ienv
                   {-# LINE 2405 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _expr2Ifresh
                   {-# LINE 2410 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _expr2Iinit
                   {-# LINE 2415 "src/JS/AG.hs" #-}
                   )
              _expr1OassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2420 "src/JS/AG.hs" #-}
                   )
              _expr1Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 2425 "src/JS/AG.hs" #-}
                   )
              _expr1OcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2430 "src/JS/AG.hs" #-}
                   )
              _expr1Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2435 "src/JS/AG.hs" #-}
                   )
              _expr1Ofinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 2440 "src/JS/AG.hs" #-}
                   )
              _expr1Ofresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2445 "src/JS/AG.hs" #-}
                   )
              _expr2OassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2450 "src/JS/AG.hs" #-}
                   )
              _expr2Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _expr1Iblocks
                   {-# LINE 2455 "src/JS/AG.hs" #-}
                   )
              _expr2OcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2460 "src/JS/AG.hs" #-}
                   )
              _expr2Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ienv
                   {-# LINE 2465 "src/JS/AG.hs" #-}
                   )
              _expr2Ofinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifinal
                   {-# LINE 2470 "src/JS/AG.hs" #-}
                   )
              _expr2Ofresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _expr1Ifresh
                   {-# LINE 2475 "src/JS/AG.hs" #-}
                   )
              ( _opIself) =
                  op_
              ( _expr1Iblocks,_expr1Ienv,_expr1IenvAVars,_expr1Ifinal,_expr1Iflow,_expr1Ifolded,_expr1Ifresh,_expr1Iinit,_expr1Iself,_expr1Ivalue,_expr1Ivars) =
                  expr1_ _expr1OanalyseData _expr1OassignResultTo _expr1Oblocks _expr1OcurrLabel _expr1Oenv _expr1Ofinal _expr1Ofresh
              ( _expr2Iblocks,_expr2Ienv,_expr2IenvAVars,_expr2Ifinal,_expr2Iflow,_expr2Ifolded,_expr2Ifresh,_expr2Iinit,_expr2Iself,_expr2Ivalue,_expr2Ivars) =
                  expr2_ _expr2OanalyseData _expr2OassignResultTo _expr2Oblocks _expr2OcurrLabel _expr2Oenv _expr2Ofinal _expr2Ofresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_UnaryAssignExpr :: T_UnaryAssignOp ->
                                  T_LValue ->
                                  T_Expression
sem_Expression_UnaryAssignExpr op_ val_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _opIself :: UnaryAssignOp
              _valIself :: LValue
              _lhsOfolded =
                  ({-# LINE 210 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 2511 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 211 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2516 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 212 "./src/JS/AG/Folding.ag" #-}
                   E _self
                   {-# LINE 2521 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 2526 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 2531 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 2536 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 2541 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 2546 "src/JS/AG.hs" #-}
                   )
              _self =
                  UnaryAssignExpr _opIself _valIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2555 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2560 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Expression.UnaryAssignExpr.lhs.init"
                   {-# LINE 2565 "src/JS/AG.hs" #-}
                   )
              ( _opIself) =
                  op_
              ( _valIself) =
                  val_
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_PrefixExpr :: T_PrefixOp ->
                             T_Expression ->
                             T_Expression
sem_Expression_PrefixExpr op_ expr_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _opIself :: PrefixOp
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 214 "./src/JS/AG/Folding.ag" #-}
                   PrefixExpr _opIself _exprIfolded
                   {-# LINE 2616 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 215 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2621 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 216 "./src/JS/AG/Folding.ag" #-}
                   E _self
                   {-# LINE 2626 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 2631 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars
                   {-# LINE 2636 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _exprIfinal
                   {-# LINE 2641 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _exprIflow
                   {-# LINE 2646 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars
                   {-# LINE 2651 "src/JS/AG.hs" #-}
                   )
              _self =
                  PrefixExpr _opIself _exprIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 2660 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _exprIfresh
                   {-# LINE 2665 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _exprIinit
                   {-# LINE 2670 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2675 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 2680 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2685 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2690 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 2695 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2700 "src/JS/AG.hs" #-}
                   )
              ( _opIself) =
                  op_
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_CallExpr :: String ->
                           T_Expressions ->
                           T_Expression
sem_Expression_CallExpr name_ params_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _lhsOfolded :: Expression
              _paramsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOenvAVars :: EnvAVars
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _paramsOassignResultTo :: (Maybe String)
              _paramsOblocks :: (M.Map Label Block)
              _paramsOcurrLabel :: Int
              _paramsOenv :: InternalFuncEnv
              _paramsOfinal :: (S.Set Label)
              _paramsOfresh :: Labels
              _paramsIblocks :: (M.Map Label Block)
              _paramsIenv :: InternalFuncEnv
              _paramsIenvAVars :: EnvAVars
              _paramsIfinal :: (S.Set Label)
              _paramsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _paramsIfolded :: Expressions
              _paramsIfresh :: Labels
              _paramsIinit :: (Maybe Label)
              _paramsIself :: Expressions
              _paramsIvars :: AVars
              _cLbl =
                  ({-# LINE 250 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 2749 "src/JS/AG.hs" #-}
                   )
              _rLbl =
                  ({-# LINE 251 "./src/JS/AG/Flow.ag" #-}
                   head $ tail _lhsIfresh
                   {-# LINE 2754 "src/JS/AG.hs" #-}
                   )
              (_nF,_xF,_) =
                  ({-# LINE 253 "./src/JS/AG/Flow.ag" #-}
                   case lookup name_ _lhsIenv of
                     Just x  -> x
                     Nothing -> error ("function " ++ name_)
                   {-# LINE 2761 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 258 "./src/JS/AG/Flow.ag" #-}
                   Just _cLbl
                   {-# LINE 2766 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 259 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _rLbl
                   {-# LINE 2771 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 260 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _cLbl     (Call _cLbl     _rLbl     name_ _paramsIself) `M.union`
                   M.singleton _rLbl     (ReturnFromCall _cLbl     _rLbl     name_ _paramsIself _lhsIassignResultTo)
                   {-# LINE 2777 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 262 "./src/JS/AG/Flow.ag" #-}
                   S.singleton (Right (_cLbl    , _nF    , _xF    , _rLbl    ))
                   {-# LINE 2782 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 264 "./src/JS/AG/Flow.ag" #-}
                   drop 2 _lhsIfresh
                   {-# LINE 2787 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 218 "./src/JS/AG/Folding.ag" #-}
                   CallExpr name_ _paramsIfolded
                   {-# LINE 2792 "src/JS/AG.hs" #-}
                   )
              _paramsOanalyseData =
                  ({-# LINE 219 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2797 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 220 "./src/JS/AG/Folding.ag" #-}
                   E $ CallExpr name_ _paramsIfolded
                   {-# LINE 2802 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _paramsIenvAVars
                   {-# LINE 2807 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _paramsIvars
                   {-# LINE 2812 "src/JS/AG.hs" #-}
                   )
              _self =
                  CallExpr name_ _paramsIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _paramsIenv
                   {-# LINE 2821 "src/JS/AG.hs" #-}
                   )
              _paramsOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2826 "src/JS/AG.hs" #-}
                   )
              _paramsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 2831 "src/JS/AG.hs" #-}
                   )
              _paramsOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2836 "src/JS/AG.hs" #-}
                   )
              _paramsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2841 "src/JS/AG.hs" #-}
                   )
              _paramsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 2846 "src/JS/AG.hs" #-}
                   )
              _paramsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2851 "src/JS/AG.hs" #-}
                   )
              ( _paramsIblocks,_paramsIenv,_paramsIenvAVars,_paramsIfinal,_paramsIflow,_paramsIfolded,_paramsIfresh,_paramsIinit,_paramsIself,_paramsIvars) =
                  params_ _paramsOanalyseData _paramsOassignResultTo _paramsOblocks _paramsOcurrLabel _paramsOenv _paramsOfinal _paramsOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
sem_Expression_ReturnFromCallExpr :: String ->
                                     T_Expressions ->
                                     T_Expression
sem_Expression_ReturnFromCallExpr name_ params_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOfolded :: Expression
              _paramsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOvalue :: ExprValue
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expression
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _paramsOassignResultTo :: (Maybe String)
              _paramsOblocks :: (M.Map Label Block)
              _paramsOcurrLabel :: Int
              _paramsOenv :: InternalFuncEnv
              _paramsOfinal :: (S.Set Label)
              _paramsOfresh :: Labels
              _paramsIblocks :: (M.Map Label Block)
              _paramsIenv :: InternalFuncEnv
              _paramsIenvAVars :: EnvAVars
              _paramsIfinal :: (S.Set Label)
              _paramsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _paramsIfolded :: Expressions
              _paramsIfresh :: Labels
              _paramsIinit :: (Maybe Label)
              _paramsIself :: Expressions
              _paramsIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 222 "./src/JS/AG/Folding.ag" #-}
                   ReturnFromCallExpr name_ _paramsIfolded
                   {-# LINE 2898 "src/JS/AG.hs" #-}
                   )
              _paramsOanalyseData =
                  ({-# LINE 223 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 2903 "src/JS/AG.hs" #-}
                   )
              _lhsOvalue =
                  ({-# LINE 224 "./src/JS/AG/Folding.ag" #-}
                   E $ ReturnFromCallExpr name_ _paramsIfolded
                   {-# LINE 2908 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _paramsIblocks
                   {-# LINE 2913 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _paramsIenvAVars
                   {-# LINE 2918 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _paramsIfinal
                   {-# LINE 2923 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _paramsIflow
                   {-# LINE 2928 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _paramsIvars
                   {-# LINE 2933 "src/JS/AG.hs" #-}
                   )
              _self =
                  ReturnFromCallExpr name_ _paramsIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _paramsIenv
                   {-# LINE 2942 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _paramsIfresh
                   {-# LINE 2947 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _paramsIinit
                   {-# LINE 2952 "src/JS/AG.hs" #-}
                   )
              _paramsOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   _lhsIassignResultTo
                   {-# LINE 2957 "src/JS/AG.hs" #-}
                   )
              _paramsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 2962 "src/JS/AG.hs" #-}
                   )
              _paramsOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 2967 "src/JS/AG.hs" #-}
                   )
              _paramsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 2972 "src/JS/AG.hs" #-}
                   )
              _paramsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 2977 "src/JS/AG.hs" #-}
                   )
              _paramsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 2982 "src/JS/AG.hs" #-}
                   )
              ( _paramsIblocks,_paramsIenv,_paramsIenvAVars,_paramsIfinal,_paramsIflow,_paramsIfolded,_paramsIfresh,_paramsIinit,_paramsIself,_paramsIvars) =
                  params_ _paramsOanalyseData _paramsOassignResultTo _paramsOblocks _paramsOcurrLabel _paramsOenv _paramsOfinal _paramsOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvalue,_lhsOvars)))
-- Expressions -------------------------------------------------
type Expressions = [Expression]
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list))
-- semantic domain
type T_Expressions = ([(Int,[Int],String,ZTB)]) ->
                     (Maybe String) ->
                     (M.Map Label Block) ->
                     Int ->
                     InternalFuncEnv ->
                     (S.Set Label) ->
                     Labels ->
                     ( (M.Map Label Block),InternalFuncEnv,EnvAVars,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),Expressions,Labels,(Maybe Label),Expressions,AVars)
data Inh_Expressions = Inh_Expressions {analyseData_Inh_Expressions :: ([(Int,[Int],String,ZTB)]),assignResultTo_Inh_Expressions :: (Maybe String),blocks_Inh_Expressions :: (M.Map Label Block),currLabel_Inh_Expressions :: Int,env_Inh_Expressions :: InternalFuncEnv,final_Inh_Expressions :: (S.Set Label),fresh_Inh_Expressions :: Labels}
data Syn_Expressions = Syn_Expressions {blocks_Syn_Expressions :: (M.Map Label Block),env_Syn_Expressions :: InternalFuncEnv,envAVars_Syn_Expressions :: EnvAVars,final_Syn_Expressions :: (S.Set Label),flow_Syn_Expressions :: (S.Set (Either FlowEdge InterFlowEntry)),folded_Syn_Expressions :: Expressions,fresh_Syn_Expressions :: Labels,init_Syn_Expressions :: (Maybe Label),self_Syn_Expressions :: Expressions,vars_Syn_Expressions :: AVars}
wrap_Expressions :: T_Expressions ->
                    Inh_Expressions ->
                    Syn_Expressions
wrap_Expressions sem (Inh_Expressions _lhsIanalyseData _lhsIassignResultTo _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh) =
    (let ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars) = sem _lhsIanalyseData _lhsIassignResultTo _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh
     in  (Syn_Expressions _lhsOblocks _lhsOenv _lhsOenvAVars _lhsOfinal _lhsOflow _lhsOfolded _lhsOfresh _lhsOinit _lhsOself _lhsOvars))
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_ =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _hdOassignResultTo :: (Maybe String)
              _tlOassignResultTo :: (Maybe String)
              _lhsOfolded :: Expressions
              _hdOanalyseData :: ([(Int,[Int],String,ZTB)])
              _tlOanalyseData :: ([(Int,[Int],String,ZTB)])
              _hdOcurrLabel :: Int
              _tlOcurrLabel :: Int
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expressions
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _hdOblocks :: (M.Map Label Block)
              _hdOenv :: InternalFuncEnv
              _hdOfinal :: (S.Set Label)
              _hdOfresh :: Labels
              _tlOblocks :: (M.Map Label Block)
              _tlOenv :: InternalFuncEnv
              _tlOfinal :: (S.Set Label)
              _tlOfresh :: Labels
              _hdIblocks :: (M.Map Label Block)
              _hdIenv :: InternalFuncEnv
              _hdIenvAVars :: EnvAVars
              _hdIfinal :: (S.Set Label)
              _hdIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _hdIfolded :: Expression
              _hdIfresh :: Labels
              _hdIinit :: (Maybe Label)
              _hdIself :: Expression
              _hdIvalue :: ExprValue
              _hdIvars :: AVars
              _tlIblocks :: (M.Map Label Block)
              _tlIenv :: InternalFuncEnv
              _tlIenvAVars :: EnvAVars
              _tlIfinal :: (S.Set Label)
              _tlIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _tlIfolded :: Expressions
              _tlIfresh :: Labels
              _tlIinit :: (Maybe Label)
              _tlIself :: Expressions
              _tlIvars :: AVars
              _hdOassignResultTo =
                  ({-# LINE 92 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 3070 "src/JS/AG.hs" #-}
                   )
              _tlOassignResultTo =
                  ({-# LINE 93 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 3075 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 46 "./src/JS/AG/Folding.ag" #-}
                   _hdIfolded : _tlIfolded
                   {-# LINE 3080 "src/JS/AG.hs" #-}
                   )
              _hdOanalyseData =
                  ({-# LINE 47 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 3085 "src/JS/AG.hs" #-}
                   )
              _tlOanalyseData =
                  ({-# LINE 48 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 3090 "src/JS/AG.hs" #-}
                   )
              _hdOcurrLabel =
                  ({-# LINE 49 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 3095 "src/JS/AG.hs" #-}
                   )
              _tlOcurrLabel =
                  ({-# LINE 50 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 3100 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks `M.union` _tlIblocks
                   {-# LINE 3105 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _hdIenvAVars `M.union` _tlIenvAVars
                   {-# LINE 3110 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _hdIfinal `S.union` _tlIfinal
                   {-# LINE 3115 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _hdIflow `S.union` _tlIflow
                   {-# LINE 3120 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _hdIvars `S.union` _tlIvars
                   {-# LINE 3125 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _tlIenv
                   {-# LINE 3134 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _tlIfresh
                   {-# LINE 3139 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _tlIinit
                   {-# LINE 3144 "src/JS/AG.hs" #-}
                   )
              _hdOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 3149 "src/JS/AG.hs" #-}
                   )
              _hdOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 3154 "src/JS/AG.hs" #-}
                   )
              _hdOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 3159 "src/JS/AG.hs" #-}
                   )
              _hdOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 3164 "src/JS/AG.hs" #-}
                   )
              _tlOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks
                   {-# LINE 3169 "src/JS/AG.hs" #-}
                   )
              _tlOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _hdIenv
                   {-# LINE 3174 "src/JS/AG.hs" #-}
                   )
              _tlOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _hdIfinal
                   {-# LINE 3179 "src/JS/AG.hs" #-}
                   )
              _tlOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _hdIfresh
                   {-# LINE 3184 "src/JS/AG.hs" #-}
                   )
              ( _hdIblocks,_hdIenv,_hdIenvAVars,_hdIfinal,_hdIflow,_hdIfolded,_hdIfresh,_hdIinit,_hdIself,_hdIvalue,_hdIvars) =
                  hd_ _hdOanalyseData _hdOassignResultTo _hdOblocks _hdOcurrLabel _hdOenv _hdOfinal _hdOfresh
              ( _tlIblocks,_tlIenv,_tlIenvAVars,_tlIfinal,_tlIflow,_tlIfolded,_tlIfresh,_tlIinit,_tlIself,_tlIvars) =
                  tl_ _tlOanalyseData _tlOassignResultTo _tlOblocks _tlOcurrLabel _tlOenv _tlOfinal _tlOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil =
    (\ _lhsIanalyseData
       _lhsIassignResultTo
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOfolded :: Expressions
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Expressions
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit =
                  ({-# LINE 89 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 3213 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 90 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 3218 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 45 "./src/JS/AG/Folding.ag" #-}
                   []
                   {-# LINE 3223 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 3228 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 3233 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 3238 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 3243 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 3252 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 3257 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
-- InfixOp -----------------------------------------------------
data InfixOp = OpLT
             | OpLEq
             | OpGT
             | OpGEq
             | OpEq
             | OpNEq
             | OpStrictEq
             | OpStrictNEq
             | OpLAnd
             | OpLOr
             | OpMul
             | OpDiv
             | OpMod
             | OpSub
             | OpLShift
             | OpSpRShift
             | OpZfRShift
             | OpBAnd
             | OpBXor
             | OpBOr
             | OpAdd
-- cata
sem_InfixOp :: InfixOp ->
               T_InfixOp
sem_InfixOp (OpLT) =
    (sem_InfixOp_OpLT)
sem_InfixOp (OpLEq) =
    (sem_InfixOp_OpLEq)
sem_InfixOp (OpGT) =
    (sem_InfixOp_OpGT)
sem_InfixOp (OpGEq) =
    (sem_InfixOp_OpGEq)
sem_InfixOp (OpEq) =
    (sem_InfixOp_OpEq)
sem_InfixOp (OpNEq) =
    (sem_InfixOp_OpNEq)
sem_InfixOp (OpStrictEq) =
    (sem_InfixOp_OpStrictEq)
sem_InfixOp (OpStrictNEq) =
    (sem_InfixOp_OpStrictNEq)
sem_InfixOp (OpLAnd) =
    (sem_InfixOp_OpLAnd)
sem_InfixOp (OpLOr) =
    (sem_InfixOp_OpLOr)
sem_InfixOp (OpMul) =
    (sem_InfixOp_OpMul)
sem_InfixOp (OpDiv) =
    (sem_InfixOp_OpDiv)
sem_InfixOp (OpMod) =
    (sem_InfixOp_OpMod)
sem_InfixOp (OpSub) =
    (sem_InfixOp_OpSub)
sem_InfixOp (OpLShift) =
    (sem_InfixOp_OpLShift)
sem_InfixOp (OpSpRShift) =
    (sem_InfixOp_OpSpRShift)
sem_InfixOp (OpZfRShift) =
    (sem_InfixOp_OpZfRShift)
sem_InfixOp (OpBAnd) =
    (sem_InfixOp_OpBAnd)
sem_InfixOp (OpBXor) =
    (sem_InfixOp_OpBXor)
sem_InfixOp (OpBOr) =
    (sem_InfixOp_OpBOr)
sem_InfixOp (OpAdd) =
    (sem_InfixOp_OpAdd)
-- semantic domain
type T_InfixOp = ( InfixOp)
data Inh_InfixOp = Inh_InfixOp {}
data Syn_InfixOp = Syn_InfixOp {self_Syn_InfixOp :: InfixOp}
wrap_InfixOp :: T_InfixOp ->
                Inh_InfixOp ->
                Syn_InfixOp
wrap_InfixOp sem (Inh_InfixOp) =
    (let ( _lhsOself) = sem
     in  (Syn_InfixOp _lhsOself))
sem_InfixOp_OpLT :: T_InfixOp
sem_InfixOp_OpLT =
    (let _lhsOself :: InfixOp
         _self =
             OpLT
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpLEq :: T_InfixOp
sem_InfixOp_OpLEq =
    (let _lhsOself :: InfixOp
         _self =
             OpLEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpGT :: T_InfixOp
sem_InfixOp_OpGT =
    (let _lhsOself :: InfixOp
         _self =
             OpGT
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpGEq :: T_InfixOp
sem_InfixOp_OpGEq =
    (let _lhsOself :: InfixOp
         _self =
             OpGEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpEq :: T_InfixOp
sem_InfixOp_OpEq =
    (let _lhsOself :: InfixOp
         _self =
             OpEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpNEq :: T_InfixOp
sem_InfixOp_OpNEq =
    (let _lhsOself :: InfixOp
         _self =
             OpNEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpStrictEq :: T_InfixOp
sem_InfixOp_OpStrictEq =
    (let _lhsOself :: InfixOp
         _self =
             OpStrictEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpStrictNEq :: T_InfixOp
sem_InfixOp_OpStrictNEq =
    (let _lhsOself :: InfixOp
         _self =
             OpStrictNEq
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpLAnd :: T_InfixOp
sem_InfixOp_OpLAnd =
    (let _lhsOself :: InfixOp
         _self =
             OpLAnd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpLOr :: T_InfixOp
sem_InfixOp_OpLOr =
    (let _lhsOself :: InfixOp
         _self =
             OpLOr
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpMul :: T_InfixOp
sem_InfixOp_OpMul =
    (let _lhsOself :: InfixOp
         _self =
             OpMul
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpDiv :: T_InfixOp
sem_InfixOp_OpDiv =
    (let _lhsOself :: InfixOp
         _self =
             OpDiv
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpMod :: T_InfixOp
sem_InfixOp_OpMod =
    (let _lhsOself :: InfixOp
         _self =
             OpMod
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpSub :: T_InfixOp
sem_InfixOp_OpSub =
    (let _lhsOself :: InfixOp
         _self =
             OpSub
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpLShift :: T_InfixOp
sem_InfixOp_OpLShift =
    (let _lhsOself :: InfixOp
         _self =
             OpLShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpSpRShift :: T_InfixOp
sem_InfixOp_OpSpRShift =
    (let _lhsOself :: InfixOp
         _self =
             OpSpRShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpZfRShift :: T_InfixOp
sem_InfixOp_OpZfRShift =
    (let _lhsOself :: InfixOp
         _self =
             OpZfRShift
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpBAnd :: T_InfixOp
sem_InfixOp_OpBAnd =
    (let _lhsOself :: InfixOp
         _self =
             OpBAnd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpBXor :: T_InfixOp
sem_InfixOp_OpBXor =
    (let _lhsOself :: InfixOp
         _self =
             OpBXor
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpBOr :: T_InfixOp
sem_InfixOp_OpBOr =
    (let _lhsOself :: InfixOp
         _self =
             OpBOr
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_InfixOp_OpAdd :: T_InfixOp
sem_InfixOp_OpAdd =
    (let _lhsOself :: InfixOp
         _self =
             OpAdd
         _lhsOself =
             _self
     in  ( _lhsOself))
-- JavaScript --------------------------------------------------
data JavaScript = Script (Statements)
-- cata
sem_JavaScript :: JavaScript ->
                  T_JavaScript
sem_JavaScript (Script _stmts) =
    (sem_JavaScript_Script (sem_Statements _stmts))
-- semantic domain
type T_JavaScript = ( (JSControlFlow Gr),Statements,FuncEnv,EnvAVars,Label,JavaScript,AVars)
data Inh_JavaScript = Inh_JavaScript {}
data Syn_JavaScript = Syn_JavaScript {controlFlow_Syn_JavaScript :: (JSControlFlow Gr),desugared_Syn_JavaScript :: Statements,env_Syn_JavaScript :: FuncEnv,envAVars_Syn_JavaScript :: EnvAVars,extremalLabel_Syn_JavaScript :: Label,self_Syn_JavaScript :: JavaScript,vars_Syn_JavaScript :: AVars}
wrap_JavaScript :: T_JavaScript ->
                   Inh_JavaScript ->
                   Syn_JavaScript
wrap_JavaScript sem (Inh_JavaScript) =
    (let ( _lhsOcontrolFlow,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOextremalLabel,_lhsOself,_lhsOvars) = sem
     in  (Syn_JavaScript _lhsOcontrolFlow _lhsOdesugared _lhsOenv _lhsOenvAVars _lhsOextremalLabel _lhsOself _lhsOvars))
sem_JavaScript_Script :: T_Statements ->
                         T_JavaScript
sem_JavaScript_Script stmts_ =
    (let _lhsOextremalLabel :: Label
         _lhsOenv :: FuncEnv
         _lhsOcontrolFlow :: (JSControlFlow Gr)
         _stmtsOfresh :: Labels
         _stmtsOenv :: InternalFuncEnv
         _stmtsOblocks :: (M.Map Label Block)
         _stmtsOfinal :: (S.Set Label)
         _lhsOdesugared :: Statements
         _lhsOenvAVars :: EnvAVars
         _lhsOvars :: AVars
         _lhsOself :: JavaScript
         _stmtsIblocks :: (M.Map Label Block)
         _stmtsIdesugared :: Statements
         _stmtsIenv :: InternalFuncEnv
         _stmtsIenvAVars :: EnvAVars
         _stmtsIfinal :: (S.Set Label)
         _stmtsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
         _stmtsIfresh :: Labels
         _stmtsIinit :: (Maybe Label)
         _stmtsIself :: Statements
         _stmtsIvars :: AVars
         (_intraflow,_interflow) =
             ({-# LINE 44 "./src/JS/AG/Flow.ag" #-}
              partitionEithers (S.toList _stmtsIflow)
              {-# LINE 3549 "src/JS/AG.hs" #-}
              )
         _beginSkipLbl =
             ({-# LINE 48 "./src/JS/AG/Flow.ag" #-}
              head _stmtsIfresh
              {-# LINE 3554 "src/JS/AG.hs" #-}
              )
         _endSkipLbl =
             ({-# LINE 49 "./src/JS/AG/Flow.ag" #-}
              head $ tail _stmtsIfresh
              {-# LINE 3559 "src/JS/AG.hs" #-}
              )
         _extremalLabel =
             ({-# LINE 52 "./src/JS/AG/Flow.ag" #-}
              extremalLbl (M.toList _stmtsIblocks)
              {-# LINE 3564 "src/JS/AG.hs" #-}
              )
         _gr =
             ({-# LINE 54 "./src/JS/AG/Flow.ag" #-}
              (mkGraph (M.toList _stmtsIblocks) _intraflow    ) :: IntraFlow Gr Block
              {-# LINE 3569 "src/JS/AG.hs" #-}
              )
         _grWithSkip =
             ({-# LINE 56 "./src/JS/AG/Flow.ag" #-}
              let withBeginSkip = insNode (_beginSkipLbl    , Skip _beginSkipLbl    ) _gr
                  withEndSkip   = insNode (_endSkipLbl    , Skip _endSkipLbl    ) withBeginSkip
                  withBeginEdge = insEdge (_beginSkipLbl    , _extremalLabel    , Left ()) withEndSkip
              in S.fold insEdge withBeginEdge (S.map (\final -> (final, _endSkipLbl    , Left ())) _stmtsIfinal)
              {-# LINE 3577 "src/JS/AG.hs" #-}
              )
         _lhsOextremalLabel =
             ({-# LINE 61 "./src/JS/AG/Flow.ag" #-}
              _beginSkipLbl
              {-# LINE 3582 "src/JS/AG.hs" #-}
              )
         _lhsOenv =
             ({-# LINE 62 "./src/JS/AG/Flow.ag" #-}
              M.fromList _stmtsIenv
              {-# LINE 3587 "src/JS/AG.hs" #-}
              )
         _lhsOcontrolFlow =
             ({-# LINE 63 "./src/JS/AG/Flow.ag" #-}
              (_grWithSkip    , _interflow    )
              {-# LINE 3592 "src/JS/AG.hs" #-}
              )
         _stmtsOfresh =
             ({-# LINE 65 "./src/JS/AG/Flow.ag" #-}
              [0..]
              {-# LINE 3597 "src/JS/AG.hs" #-}
              )
         _stmtsOenv =
             ({-# LINE 66 "./src/JS/AG/Flow.ag" #-}
              []
              {-# LINE 3602 "src/JS/AG.hs" #-}
              )
         _stmtsOblocks =
             ({-# LINE 67 "./src/JS/AG/Flow.ag" #-}
              _stmtsIblocks
              {-# LINE 3607 "src/JS/AG.hs" #-}
              )
         _stmtsOfinal =
             ({-# LINE 68 "./src/JS/AG/Flow.ag" #-}
              S.empty
              {-# LINE 3612 "src/JS/AG.hs" #-}
              )
         _lhsOdesugared =
             ({-# LINE 16 "./src/JS/AG/Desugaring.ag" #-}
              _stmtsIdesugared
              {-# LINE 3617 "src/JS/AG.hs" #-}
              )
         _lhsOenvAVars =
             ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
              _stmtsIenvAVars
              {-# LINE 3622 "src/JS/AG.hs" #-}
              )
         _lhsOvars =
             ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
              _stmtsIvars
              {-# LINE 3627 "src/JS/AG.hs" #-}
              )
         _self =
             Script _stmtsIself
         _lhsOself =
             _self
         ( _stmtsIblocks,_stmtsIdesugared,_stmtsIenv,_stmtsIenvAVars,_stmtsIfinal,_stmtsIflow,_stmtsIfresh,_stmtsIinit,_stmtsIself,_stmtsIvars) =
             stmts_ _stmtsOblocks _stmtsOenv _stmtsOfinal _stmtsOfresh
     in  ( _lhsOcontrolFlow,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOextremalLabel,_lhsOself,_lhsOvars))
-- LValue ------------------------------------------------------
data LValue = LVar (String)
-- cata
sem_LValue :: LValue ->
              T_LValue
sem_LValue (LVar _name) =
    (sem_LValue_LVar _name)
-- semantic domain
type T_LValue = ( LValue)
data Inh_LValue = Inh_LValue {}
data Syn_LValue = Syn_LValue {self_Syn_LValue :: LValue}
wrap_LValue :: T_LValue ->
               Inh_LValue ->
               Syn_LValue
wrap_LValue sem (Inh_LValue) =
    (let ( _lhsOself) = sem
     in  (Syn_LValue _lhsOself))
sem_LValue_LVar :: String ->
                   T_LValue
sem_LValue_LVar name_ =
    (let _lhsOself :: LValue
         _self =
             LVar name_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MBreakCon ---------------------------------------------------
type MBreakCon = ( (Maybe String))
-- cata
sem_MBreakCon :: MBreakCon ->
                 T_MBreakCon
sem_MBreakCon ( x1) =
    (sem_MBreakCon_Tuple x1)
-- semantic domain
type T_MBreakCon = ( MBreakCon)
data Inh_MBreakCon = Inh_MBreakCon {}
data Syn_MBreakCon = Syn_MBreakCon {self_Syn_MBreakCon :: MBreakCon}
wrap_MBreakCon :: T_MBreakCon ->
                  Inh_MBreakCon ->
                  Syn_MBreakCon
wrap_MBreakCon sem (Inh_MBreakCon) =
    (let ( _lhsOself) = sem
     in  (Syn_MBreakCon _lhsOself))
sem_MBreakCon_Tuple :: (Maybe String) ->
                       T_MBreakCon
sem_MBreakCon_Tuple x1_ =
    (let _lhsOself :: MBreakCon
         _self =
             (x1_)
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MExpression -------------------------------------------------
data MExpression = NoExpr
                 | JustExpr (Expression)
-- cata
sem_MExpression :: MExpression ->
                   T_MExpression
sem_MExpression (NoExpr) =
    (sem_MExpression_NoExpr)
sem_MExpression (JustExpr _expr) =
    (sem_MExpression_JustExpr (sem_Expression _expr))
-- semantic domain
type T_MExpression = ([(Int,[Int],String,ZTB)]) ->
                     Int ->
                     ( MExpression,MExpression)
data Inh_MExpression = Inh_MExpression {analyseData_Inh_MExpression :: ([(Int,[Int],String,ZTB)]),currLabel_Inh_MExpression :: Int}
data Syn_MExpression = Syn_MExpression {folded_Syn_MExpression :: MExpression,self_Syn_MExpression :: MExpression}
wrap_MExpression :: T_MExpression ->
                    Inh_MExpression ->
                    Syn_MExpression
wrap_MExpression sem (Inh_MExpression _lhsIanalyseData _lhsIcurrLabel) =
    (let ( _lhsOfolded,_lhsOself) = sem _lhsIanalyseData _lhsIcurrLabel
     in  (Syn_MExpression _lhsOfolded _lhsOself))
sem_MExpression_NoExpr :: T_MExpression
sem_MExpression_NoExpr =
    (\ _lhsIanalyseData
       _lhsIcurrLabel ->
         (let _lhsOfolded :: MExpression
              _lhsOself :: MExpression
              _lhsOfolded =
                  ({-# LINE 227 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 3719 "src/JS/AG.hs" #-}
                   )
              _self =
                  NoExpr
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
sem_MExpression_JustExpr :: T_Expression ->
                            T_MExpression
sem_MExpression_JustExpr expr_ =
    (\ _lhsIanalyseData
       _lhsIcurrLabel ->
         (let _lhsOfolded :: MExpression
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _lhsOself :: MExpression
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOfolded =
                  ({-# LINE 228 "./src/JS/AG/Folding.ag" #-}
                   JustExpr _exprIfolded
                   {-# LINE 3754 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 229 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 3759 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 230 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 3764 "src/JS/AG.hs" #-}
                   )
              _self =
                  JustExpr _exprIself
              _lhsOself =
                  _self
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: MExpression.JustExpr.expr.assignResultTo"
                   {-# LINE 3773 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: MExpression.JustExpr.expr.blocks"
                   {-# LINE 3778 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: MExpression.JustExpr.expr.env"
                   {-# LINE 3783 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: MExpression.JustExpr.expr.final"
                   {-# LINE 3788 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: MExpression.JustExpr.expr.fresh"
                   {-# LINE 3793 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOfolded,_lhsOself)))
-- MExpressions ------------------------------------------------
type MExpressions = [MExpression]
-- cata
sem_MExpressions :: MExpressions ->
                    T_MExpressions
sem_MExpressions list =
    (Prelude.foldr sem_MExpressions_Cons sem_MExpressions_Nil (Prelude.map sem_MExpression list))
-- semantic domain
type T_MExpressions = ([(Int,[Int],String,ZTB)]) ->
                      Int ->
                      ( MExpressions,MExpressions)
data Inh_MExpressions = Inh_MExpressions {analyseData_Inh_MExpressions :: ([(Int,[Int],String,ZTB)]),currLabel_Inh_MExpressions :: Int}
data Syn_MExpressions = Syn_MExpressions {folded_Syn_MExpressions :: MExpressions,self_Syn_MExpressions :: MExpressions}
wrap_MExpressions :: T_MExpressions ->
                     Inh_MExpressions ->
                     Syn_MExpressions
wrap_MExpressions sem (Inh_MExpressions _lhsIanalyseData _lhsIcurrLabel) =
    (let ( _lhsOfolded,_lhsOself) = sem _lhsIanalyseData _lhsIcurrLabel
     in  (Syn_MExpressions _lhsOfolded _lhsOself))
sem_MExpressions_Cons :: T_MExpression ->
                         T_MExpressions ->
                         T_MExpressions
sem_MExpressions_Cons hd_ tl_ =
    (\ _lhsIanalyseData
       _lhsIcurrLabel ->
         (let _lhsOfolded :: MExpressions
              _hdOanalyseData :: ([(Int,[Int],String,ZTB)])
              _tlOanalyseData :: ([(Int,[Int],String,ZTB)])
              _hdOcurrLabel :: Int
              _tlOcurrLabel :: Int
              _lhsOself :: MExpressions
              _hdIfolded :: MExpression
              _hdIself :: MExpression
              _tlIfolded :: MExpressions
              _tlIself :: MExpressions
              _lhsOfolded =
                  ({-# LINE 54 "./src/JS/AG/Folding.ag" #-}
                   _hdIfolded : _tlIfolded
                   {-# LINE 3836 "src/JS/AG.hs" #-}
                   )
              _hdOanalyseData =
                  ({-# LINE 55 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 3841 "src/JS/AG.hs" #-}
                   )
              _tlOanalyseData =
                  ({-# LINE 56 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 3846 "src/JS/AG.hs" #-}
                   )
              _hdOcurrLabel =
                  ({-# LINE 57 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 3851 "src/JS/AG.hs" #-}
                   )
              _tlOcurrLabel =
                  ({-# LINE 58 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 3856 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              ( _hdIfolded,_hdIself) =
                  hd_ _hdOanalyseData _hdOcurrLabel
              ( _tlIfolded,_tlIself) =
                  tl_ _tlOanalyseData _tlOcurrLabel
          in  ( _lhsOfolded,_lhsOself)))
sem_MExpressions_Nil :: T_MExpressions
sem_MExpressions_Nil =
    (\ _lhsIanalyseData
       _lhsIcurrLabel ->
         (let _lhsOfolded :: MExpressions
              _lhsOself :: MExpressions
              _lhsOfolded =
                  ({-# LINE 53 "./src/JS/AG/Folding.ag" #-}
                   []
                   {-# LINE 3876 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOfolded,_lhsOself)))
-- MResult -----------------------------------------------------
type MResult = ( (Maybe Result))
-- cata
sem_MResult :: MResult ->
               T_MResult
sem_MResult ( x1) =
    (sem_MResult_Tuple x1)
-- semantic domain
type T_MResult = ( MResult)
data Inh_MResult = Inh_MResult {}
data Syn_MResult = Syn_MResult {self_Syn_MResult :: MResult}
wrap_MResult :: T_MResult ->
                Inh_MResult ->
                Syn_MResult
wrap_MResult sem (Inh_MResult) =
    (let ( _lhsOself) = sem
     in  (Syn_MResult _lhsOself))
sem_MResult_Tuple :: (Maybe Result) ->
                     T_MResult
sem_MResult_Tuple x1_ =
    (let _lhsOself :: MResult
         _self =
             (x1_)
         _lhsOself =
             _self
     in  ( _lhsOself))
-- PrefixOp ----------------------------------------------------
data PrefixOp = PrefixLNot
              | PrefixBNot
              | PrefixPlus
              | PrefixMinus
-- cata
sem_PrefixOp :: PrefixOp ->
                T_PrefixOp
sem_PrefixOp (PrefixLNot) =
    (sem_PrefixOp_PrefixLNot)
sem_PrefixOp (PrefixBNot) =
    (sem_PrefixOp_PrefixBNot)
sem_PrefixOp (PrefixPlus) =
    (sem_PrefixOp_PrefixPlus)
sem_PrefixOp (PrefixMinus) =
    (sem_PrefixOp_PrefixMinus)
-- semantic domain
type T_PrefixOp = ( PrefixOp)
data Inh_PrefixOp = Inh_PrefixOp {}
data Syn_PrefixOp = Syn_PrefixOp {self_Syn_PrefixOp :: PrefixOp}
wrap_PrefixOp :: T_PrefixOp ->
                 Inh_PrefixOp ->
                 Syn_PrefixOp
wrap_PrefixOp sem (Inh_PrefixOp) =
    (let ( _lhsOself) = sem
     in  (Syn_PrefixOp _lhsOself))
sem_PrefixOp_PrefixLNot :: T_PrefixOp
sem_PrefixOp_PrefixLNot =
    (let _lhsOself :: PrefixOp
         _self =
             PrefixLNot
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_PrefixOp_PrefixBNot :: T_PrefixOp
sem_PrefixOp_PrefixBNot =
    (let _lhsOself :: PrefixOp
         _self =
             PrefixBNot
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_PrefixOp_PrefixPlus :: T_PrefixOp
sem_PrefixOp_PrefixPlus =
    (let _lhsOself :: PrefixOp
         _self =
             PrefixPlus
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_PrefixOp_PrefixMinus :: T_PrefixOp
sem_PrefixOp_PrefixMinus =
    (let _lhsOself :: PrefixOp
         _self =
             PrefixMinus
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Statement ---------------------------------------------------
data Statement = EmptyStmt
               | BlockStmt (Statements)
               | ExprStmt (Expression)
               | VarDeclStmt (VarDecls)
               | BreakStmt (MBreakCon)
               | ContinueStmt (MBreakCon)
               | LabelledStmt (MBreakCon) (Statement)
               | IfStmt (Expression) (Statement) (Statement)
               | WhileStmt (Expression) (Statement)
               | ForStmt (ForInit) (MExpression) (MExpression) (Statement)
               | SwitchStmt (Expression) (CaseClauses)
               | FunctionStmt (String) (([String])) (Statement)
               | ReturnStmt (MExpression)
               | ParamStmt (String) (Expression)
-- cata
sem_Statement :: Statement ->
                 T_Statement
sem_Statement (EmptyStmt) =
    (sem_Statement_EmptyStmt)
sem_Statement (BlockStmt _stmts) =
    (sem_Statement_BlockStmt (sem_Statements _stmts))
sem_Statement (ExprStmt _expr) =
    (sem_Statement_ExprStmt (sem_Expression _expr))
sem_Statement (VarDeclStmt _decls) =
    (sem_Statement_VarDeclStmt (sem_VarDecls _decls))
sem_Statement (BreakStmt _lbl) =
    (sem_Statement_BreakStmt (sem_MBreakCon _lbl))
sem_Statement (ContinueStmt _lbl) =
    (sem_Statement_ContinueStmt (sem_MBreakCon _lbl))
sem_Statement (LabelledStmt _lbl _stmt) =
    (sem_Statement_LabelledStmt (sem_MBreakCon _lbl) (sem_Statement _stmt))
sem_Statement (IfStmt _expr _stmt1 _stmt2) =
    (sem_Statement_IfStmt (sem_Expression _expr) (sem_Statement _stmt1) (sem_Statement _stmt2))
sem_Statement (WhileStmt _expr _stmt) =
    (sem_Statement_WhileStmt (sem_Expression _expr) (sem_Statement _stmt))
sem_Statement (ForStmt _init _test _step _stmt) =
    (sem_Statement_ForStmt _init (sem_MExpression _test) (sem_MExpression _step) (sem_Statement _stmt))
sem_Statement (SwitchStmt _expr _clauses) =
    (sem_Statement_SwitchStmt (sem_Expression _expr) (sem_CaseClauses _clauses))
sem_Statement (FunctionStmt _name _params _stmt) =
    (sem_Statement_FunctionStmt _name _params (sem_Statement _stmt))
sem_Statement (ReturnStmt _expr) =
    (sem_Statement_ReturnStmt (sem_MExpression _expr))
sem_Statement (ParamStmt _name _expr) =
    (sem_Statement_ParamStmt _name (sem_Expression _expr))
-- semantic domain
type T_Statement = (M.Map Label Block) ->
                   InternalFuncEnv ->
                   (S.Set Label) ->
                   Labels ->
                   Expression ->
                   ( (M.Map Label Block),Statements,InternalFuncEnv,EnvAVars,Statements,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),Labels,(Maybe Label),Statement,AVars)
data Inh_Statement = Inh_Statement {blocks_Inh_Statement :: (M.Map Label Block),env_Inh_Statement :: InternalFuncEnv,final_Inh_Statement :: (S.Set Label),fresh_Inh_Statement :: Labels,test_Inh_Statement :: Expression}
data Syn_Statement = Syn_Statement {blocks_Syn_Statement :: (M.Map Label Block),desugared_Syn_Statement :: Statements,env_Syn_Statement :: InternalFuncEnv,envAVars_Syn_Statement :: EnvAVars,fallthrough_Syn_Statement :: Statements,final_Syn_Statement :: (S.Set Label),flow_Syn_Statement :: (S.Set (Either FlowEdge InterFlowEntry)),fresh_Syn_Statement :: Labels,init_Syn_Statement :: (Maybe Label),self_Syn_Statement :: Statement,vars_Syn_Statement :: AVars}
wrap_Statement :: T_Statement ->
                  Inh_Statement ->
                  Syn_Statement
wrap_Statement sem (Inh_Statement _lhsIblocks _lhsIenv _lhsIfinal _lhsIfresh _lhsItest) =
    (let ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars) = sem _lhsIblocks _lhsIenv _lhsIfinal _lhsIfresh _lhsItest
     in  (Syn_Statement _lhsOblocks _lhsOdesugared _lhsOenv _lhsOenvAVars _lhsOfallthrough _lhsOfinal _lhsOflow _lhsOfresh _lhsOinit _lhsOself _lhsOvars))
sem_Statement_EmptyStmt :: T_Statement
sem_Statement_EmptyStmt =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lbl =
                  ({-# LINE 112 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 4049 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 114 "./src/JS/AG/Flow.ag" #-}
                   Just _lbl
                   {-# LINE 4054 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 115 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _lbl
                   {-# LINE 4059 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 116 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _lbl     (Skip _lbl    )
                   {-# LINE 4064 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 117 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4069 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 119 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 4074 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 19 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 4079 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 4084 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4089 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 4094 "src/JS/AG.hs" #-}
                   )
              _self =
                  EmptyStmt
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4103 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_BlockStmt :: T_Statements ->
                           T_Statement
sem_Statement_BlockStmt stmts_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOinit :: (Maybe Label)
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _stmtsOenv :: InternalFuncEnv
              _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _stmtsOblocks :: (M.Map Label Block)
              _stmtsOfinal :: (S.Set Label)
              _stmtsOfresh :: Labels
              _stmtsIblocks :: (M.Map Label Block)
              _stmtsIdesugared :: Statements
              _stmtsIenv :: InternalFuncEnv
              _stmtsIenvAVars :: EnvAVars
              _stmtsIfinal :: (S.Set Label)
              _stmtsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmtsIfresh :: Labels
              _stmtsIinit :: (Maybe Label)
              _stmtsIself :: Statements
              _stmtsIvars :: AVars
              _lhsOfinal =
                  ({-# LINE 122 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIfinal
                   {-# LINE 4142 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 123 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIflow
                   {-# LINE 4147 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 124 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIinit
                   {-# LINE 4152 "src/JS/AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 125 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIenv
                   {-# LINE 4157 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 126 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIfresh
                   {-# LINE 4162 "src/JS/AG.hs" #-}
                   )
              _stmtsOenv =
                  ({-# LINE 127 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4167 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 26 "./src/JS/AG/Desugaring.ag" #-}
                   [BlockStmt _stmtsIdesugared]
                   {-# LINE 4172 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _stmtsIblocks
                   {-# LINE 4177 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtsIenvAVars
                   {-# LINE 4182 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4187 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtsIvars
                   {-# LINE 4192 "src/JS/AG.hs" #-}
                   )
              _self =
                  BlockStmt _stmtsIself
              _lhsOself =
                  _self
              _stmtsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 4201 "src/JS/AG.hs" #-}
                   )
              _stmtsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 4206 "src/JS/AG.hs" #-}
                   )
              _stmtsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4211 "src/JS/AG.hs" #-}
                   )
              ( _stmtsIblocks,_stmtsIdesugared,_stmtsIenv,_stmtsIenvAVars,_stmtsIfinal,_stmtsIflow,_stmtsIfresh,_stmtsIinit,_stmtsIself,_stmtsIvars) =
                  stmts_ _stmtsOblocks _stmtsOenv _stmtsOfinal _stmtsOfresh
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_ExprStmt :: T_Expression ->
                          T_Statement
sem_Statement_ExprStmt expr_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _exprOassignResultTo :: (Maybe String)
              _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _exprOassignResultTo =
                  ({-# LINE 130 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 4256 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 20 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 4261 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 4266 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars
                   {-# LINE 4271 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4276 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _exprIfinal
                   {-# LINE 4281 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _exprIflow
                   {-# LINE 4286 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars
                   {-# LINE 4291 "src/JS/AG.hs" #-}
                   )
              _self =
                  ExprStmt _exprIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 4300 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _exprIfresh
                   {-# LINE 4305 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _exprIinit
                   {-# LINE 4310 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ExprStmt.expr.analyseData"
                   {-# LINE 4315 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 4320 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ExprStmt.expr.currLabel"
                   {-# LINE 4325 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4330 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 4335 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4340 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_VarDeclStmt :: T_VarDecls ->
                             T_Statement
sem_Statement_VarDeclStmt decls_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _declsOanalyseData :: ([(Int,[Int],String,ZTB)])
              _declsOblocks :: (M.Map Label Block)
              _declsOcurrLabel :: Int
              _declsOenv :: InternalFuncEnv
              _declsOfinal :: (S.Set Label)
              _declsOfresh :: Labels
              _declsIblocks :: (M.Map Label Block)
              _declsIenv :: InternalFuncEnv
              _declsIfinal :: (S.Set Label)
              _declsIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _declsIfolded :: VarDecls
              _declsIfresh :: Labels
              _declsIinit :: (Maybe Label)
              _declsIself :: VarDecls
              _lhsOdesugared =
                  ({-# LINE 21 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 4381 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _declsIblocks
                   {-# LINE 4386 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 4391 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4396 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _declsIfinal
                   {-# LINE 4401 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _declsIflow
                   {-# LINE 4406 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 4411 "src/JS/AG.hs" #-}
                   )
              _self =
                  VarDeclStmt _declsIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _declsIenv
                   {-# LINE 4420 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _declsIfresh
                   {-# LINE 4425 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _declsIinit
                   {-# LINE 4430 "src/JS/AG.hs" #-}
                   )
              _declsOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.VarDeclStmt.decls.analyseData"
                   {-# LINE 4435 "src/JS/AG.hs" #-}
                   )
              _declsOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 4440 "src/JS/AG.hs" #-}
                   )
              _declsOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.VarDeclStmt.decls.currLabel"
                   {-# LINE 4445 "src/JS/AG.hs" #-}
                   )
              _declsOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4450 "src/JS/AG.hs" #-}
                   )
              _declsOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 4455 "src/JS/AG.hs" #-}
                   )
              _declsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4460 "src/JS/AG.hs" #-}
                   )
              ( _declsIblocks,_declsIenv,_declsIfinal,_declsIflow,_declsIfolded,_declsIfresh,_declsIinit,_declsIself) =
                  decls_ _declsOanalyseData _declsOblocks _declsOcurrLabel _declsOenv _declsOfinal _declsOfresh
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_BreakStmt :: T_MBreakCon ->
                           T_Statement
sem_Statement_BreakStmt lbl_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lblIself :: MBreakCon
              _lhsOdesugared =
                  ({-# LINE 22 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 4488 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 4493 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 4498 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4503 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4508 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4513 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 4518 "src/JS/AG.hs" #-}
                   )
              _self =
                  BreakStmt _lblIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4527 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4532 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.BreakStmt.lhs.init"
                   {-# LINE 4537 "src/JS/AG.hs" #-}
                   )
              ( _lblIself) =
                  lbl_
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_ContinueStmt :: T_MBreakCon ->
                              T_Statement
sem_Statement_ContinueStmt lbl_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _lblIself :: MBreakCon
              _lhsOdesugared =
                  ({-# LINE 23 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 4565 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 4570 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 4575 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 4580 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4585 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4590 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 4595 "src/JS/AG.hs" #-}
                   )
              _self =
                  ContinueStmt _lblIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4604 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4609 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.ContinueStmt.lhs.init"
                   {-# LINE 4614 "src/JS/AG.hs" #-}
                   )
              ( _lblIself) =
                  lbl_
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_LabelledStmt :: T_MBreakCon ->
                              T_Statement ->
                              T_Statement
sem_Statement_LabelledStmt lbl_ stmt_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _stmtOblocks :: (M.Map Label Block)
              _stmtOenv :: InternalFuncEnv
              _stmtOfinal :: (S.Set Label)
              _stmtOfresh :: Labels
              _stmtOtest :: Expression
              _lblIself :: MBreakCon
              _stmtIblocks :: (M.Map Label Block)
              _stmtIdesugared :: Statements
              _stmtIenv :: InternalFuncEnv
              _stmtIenvAVars :: EnvAVars
              _stmtIfallthrough :: Statements
              _stmtIfinal :: (S.Set Label)
              _stmtIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmtIfresh :: Labels
              _stmtIinit :: (Maybe Label)
              _stmtIself :: Statement
              _stmtIvars :: AVars
              _lhsOdesugared =
                  ({-# LINE 27 "./src/JS/AG/Desugaring.ag" #-}
                   [LabelledStmt lbl_ (BlockStmt _stmtIdesugared)]
                   {-# LINE 4659 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _stmtIblocks
                   {-# LINE 4664 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtIenvAVars
                   {-# LINE 4669 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _stmtIfallthrough
                   {-# LINE 4674 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _stmtIfinal
                   {-# LINE 4679 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _stmtIflow
                   {-# LINE 4684 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtIvars
                   {-# LINE 4689 "src/JS/AG.hs" #-}
                   )
              _self =
                  LabelledStmt _lblIself _stmtIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _stmtIenv
                   {-# LINE 4698 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _stmtIfresh
                   {-# LINE 4703 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _stmtIinit
                   {-# LINE 4708 "src/JS/AG.hs" #-}
                   )
              _stmtOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 4713 "src/JS/AG.hs" #-}
                   )
              _stmtOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4718 "src/JS/AG.hs" #-}
                   )
              _stmtOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 4723 "src/JS/AG.hs" #-}
                   )
              _stmtOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4728 "src/JS/AG.hs" #-}
                   )
              _stmtOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 4733 "src/JS/AG.hs" #-}
                   )
              ( _lblIself) =
                  lbl_
              ( _stmtIblocks,_stmtIdesugared,_stmtIenv,_stmtIenvAVars,_stmtIfallthrough,_stmtIfinal,_stmtIflow,_stmtIfresh,_stmtIinit,_stmtIself,_stmtIvars) =
                  stmt_ _stmtOblocks _stmtOenv _stmtOfinal _stmtOfresh _stmtOtest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_IfStmt :: T_Expression ->
                        T_Statement ->
                        T_Statement ->
                        T_Statement
sem_Statement_IfStmt expr_ stmt1_ stmt2_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmt1Ofresh :: Labels
              _stmt2Ofresh :: Labels
              _stmt1Ofinal :: (S.Set Label)
              _stmt2Ofinal :: (S.Set Label)
              _lhsOfresh :: Labels
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _stmt1Oblocks :: (M.Map Label Block)
              _stmt1Oenv :: InternalFuncEnv
              _stmt1Otest :: Expression
              _stmt2Oblocks :: (M.Map Label Block)
              _stmt2Oenv :: InternalFuncEnv
              _stmt2Otest :: Expression
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _stmt1Iblocks :: (M.Map Label Block)
              _stmt1Idesugared :: Statements
              _stmt1Ienv :: InternalFuncEnv
              _stmt1IenvAVars :: EnvAVars
              _stmt1Ifallthrough :: Statements
              _stmt1Ifinal :: (S.Set Label)
              _stmt1Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmt1Ifresh :: Labels
              _stmt1Iinit :: (Maybe Label)
              _stmt1Iself :: Statement
              _stmt1Ivars :: AVars
              _stmt2Iblocks :: (M.Map Label Block)
              _stmt2Idesugared :: Statements
              _stmt2Ienv :: InternalFuncEnv
              _stmt2IenvAVars :: EnvAVars
              _stmt2Ifallthrough :: Statements
              _stmt2Ifinal :: (S.Set Label)
              _stmt2Iflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmt2Ifresh :: Labels
              _stmt2Iinit :: (Maybe Label)
              _stmt2Iself :: Statement
              _stmt2Ivars :: AVars
              _condLbl =
                  ({-# LINE 185 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 4814 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 187 "./src/JS/AG/Flow.ag" #-}
                   Just _condLbl
                   {-# LINE 4819 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 189 "./src/JS/AG/Flow.ag" #-}
                   case (S.null _stmt1Ifinal, S.null _stmt2Ifinal) of
                     (True,True)   -> S.singleton _condLbl
                     (True,False)  -> S.singleton _condLbl     `S.union` _stmt2Ifinal
                     (False,True)  -> S.singleton _condLbl     `S.union` _stmt1Ifinal
                     (False,False) -> _stmt1Ifinal `S.union` _stmt2Ifinal
                   {-# LINE 4828 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 196 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _condLbl     (If _condLbl     _exprIself) `M.union` _stmt1Iblocks `M.union` _stmt2Iblocks
                   {-# LINE 4833 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 198 "./src/JS/AG/Flow.ag" #-}
                   case (isNothing _stmt1Iinit, isNothing _stmt2Iinit) of
                     (True,True)   -> S.empty
                     (False,True)  -> _stmt1Iflow `S.union` S.singleton (_condLbl     |-> (fromJust _stmt1Iinit))
                     (True,False)  -> _stmt2Iflow `S.union` S.singleton (_condLbl     |-> (fromJust _stmt2Iinit))
                     (False,False) -> _stmt1Iflow `S.union` _stmt2Iflow `S.union`
                                      S.singleton (_condLbl     |-> (fromJust _stmt1Iinit)) `S.union`
                                      S.singleton (_condLbl     |-> (fromJust _stmt2Iinit))
                   {-# LINE 4844 "src/JS/AG.hs" #-}
                   )
              _stmt1Ofresh =
                  ({-# LINE 206 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 4849 "src/JS/AG.hs" #-}
                   )
              _stmt2Ofresh =
                  ({-# LINE 207 "./src/JS/AG/Flow.ag" #-}
                   _stmt1Ifresh
                   {-# LINE 4854 "src/JS/AG.hs" #-}
                   )
              _stmt1Ofinal =
                  ({-# LINE 209 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4859 "src/JS/AG.hs" #-}
                   )
              _stmt2Ofinal =
                  ({-# LINE 210 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 4864 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 212 "./src/JS/AG/Flow.ag" #-}
                   _stmt2Ifresh
                   {-# LINE 4869 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 28 "./src/JS/AG/Desugaring.ag" #-}
                   [IfStmt _exprIself (BlockStmt _stmt1Idesugared) (BlockStmt _stmt2Idesugared)]
                   {-# LINE 4874 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars `M.union` _stmt1IenvAVars `M.union` _stmt2IenvAVars
                   {-# LINE 4879 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _stmt1Ifallthrough ++ _stmt2Ifallthrough
                   {-# LINE 4884 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars `S.union` _stmt1Ivars `S.union` _stmt2Ivars
                   {-# LINE 4889 "src/JS/AG.hs" #-}
                   )
              _self =
                  IfStmt _exprIself _stmt1Iself _stmt2Iself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _stmt2Ienv
                   {-# LINE 4898 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.IfStmt.expr.analyseData"
                   {-# LINE 4903 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.IfStmt.expr.assignResultTo"
                   {-# LINE 4908 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 4913 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.IfStmt.expr.currLabel"
                   {-# LINE 4918 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 4923 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 4928 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 4933 "src/JS/AG.hs" #-}
                   )
              _stmt1Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 4938 "src/JS/AG.hs" #-}
                   )
              _stmt1Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 4943 "src/JS/AG.hs" #-}
                   )
              _stmt1Otest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 4948 "src/JS/AG.hs" #-}
                   )
              _stmt2Oblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _stmt1Iblocks
                   {-# LINE 4953 "src/JS/AG.hs" #-}
                   )
              _stmt2Oenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _stmt1Ienv
                   {-# LINE 4958 "src/JS/AG.hs" #-}
                   )
              _stmt2Otest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 4963 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
              ( _stmt1Iblocks,_stmt1Idesugared,_stmt1Ienv,_stmt1IenvAVars,_stmt1Ifallthrough,_stmt1Ifinal,_stmt1Iflow,_stmt1Ifresh,_stmt1Iinit,_stmt1Iself,_stmt1Ivars) =
                  stmt1_ _stmt1Oblocks _stmt1Oenv _stmt1Ofinal _stmt1Ofresh _stmt1Otest
              ( _stmt2Iblocks,_stmt2Idesugared,_stmt2Ienv,_stmt2IenvAVars,_stmt2Ifallthrough,_stmt2Ifinal,_stmt2Iflow,_stmt2Ifresh,_stmt2Iinit,_stmt2Iself,_stmt2Ivars) =
                  stmt2_ _stmt2Oblocks _stmt2Oenv _stmt2Ofinal _stmt2Ofresh _stmt2Otest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_WhileStmt :: T_Expression ->
                           T_Statement ->
                           T_Statement
sem_Statement_WhileStmt expr_ stmt_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _stmtOfresh :: Labels
              _stmtOfinal :: (S.Set Label)
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _stmtOblocks :: (M.Map Label Block)
              _stmtOenv :: InternalFuncEnv
              _stmtOtest :: Expression
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _stmtIblocks :: (M.Map Label Block)
              _stmtIdesugared :: Statements
              _stmtIenv :: InternalFuncEnv
              _stmtIenvAVars :: EnvAVars
              _stmtIfallthrough :: Statements
              _stmtIfinal :: (S.Set Label)
              _stmtIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmtIfresh :: Labels
              _stmtIinit :: (Maybe Label)
              _stmtIself :: Statement
              _stmtIvars :: AVars
              _condLbl =
                  ({-# LINE 167 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 5029 "src/JS/AG.hs" #-}
                   )
              _eLbl =
                  ({-# LINE 168 "./src/JS/AG/Flow.ag" #-}
                   head _stmtIfresh
                   {-# LINE 5034 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 170 "./src/JS/AG/Flow.ag" #-}
                   Just _condLbl
                   {-# LINE 5039 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 171 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _condLbl
                   {-# LINE 5044 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 172 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _condLbl     (While _condLbl     _exprIself) `M.union` _stmtIblocks
                   {-# LINE 5049 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 173 "./src/JS/AG/Flow.ag" #-}
                   case isNothing _stmtIinit of
                    True  -> S.singleton (_condLbl     |-> _condLbl    )
                    False -> _stmtIflow `S.union`
                             S.singleton (_condLbl     |-> (fromJust _stmtIinit)) `S.union`
                             S.map (\final -> final |-> _condLbl    ) _stmtIfinal
                   {-# LINE 5058 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 179 "./src/JS/AG/Flow.ag" #-}
                   _stmtIfresh
                   {-# LINE 5063 "src/JS/AG.hs" #-}
                   )
              _stmtOfresh =
                  ({-# LINE 181 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 5068 "src/JS/AG.hs" #-}
                   )
              _stmtOfinal =
                  ({-# LINE 182 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _condLbl
                   {-# LINE 5073 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 29 "./src/JS/AG/Desugaring.ag" #-}
                   [WhileStmt _exprIself (BlockStmt _stmtIdesugared)]
                   {-# LINE 5078 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars `M.union` _stmtIenvAVars
                   {-# LINE 5083 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _stmtIfallthrough
                   {-# LINE 5088 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars `S.union` _stmtIvars
                   {-# LINE 5093 "src/JS/AG.hs" #-}
                   )
              _self =
                  WhileStmt _exprIself _stmtIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _stmtIenv
                   {-# LINE 5102 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.WhileStmt.expr.analyseData"
                   {-# LINE 5107 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.WhileStmt.expr.assignResultTo"
                   {-# LINE 5112 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5117 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.WhileStmt.expr.currLabel"
                   {-# LINE 5122 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5127 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5132 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 5137 "src/JS/AG.hs" #-}
                   )
              _stmtOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 5142 "src/JS/AG.hs" #-}
                   )
              _stmtOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 5147 "src/JS/AG.hs" #-}
                   )
              _stmtOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 5152 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
              ( _stmtIblocks,_stmtIdesugared,_stmtIenv,_stmtIenvAVars,_stmtIfallthrough,_stmtIfinal,_stmtIflow,_stmtIfresh,_stmtIinit,_stmtIself,_stmtIvars) =
                  stmt_ _stmtOblocks _stmtOenv _stmtOfinal _stmtOfresh _stmtOtest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_ForStmt :: ForInit ->
                         T_MExpression ->
                         T_MExpression ->
                         T_Statement ->
                         T_Statement
sem_Statement_ForStmt init_ test_ step_ stmt_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _testOanalyseData :: ([(Int,[Int],String,ZTB)])
              _testOcurrLabel :: Int
              _stepOanalyseData :: ([(Int,[Int],String,ZTB)])
              _stepOcurrLabel :: Int
              _stmtOblocks :: (M.Map Label Block)
              _stmtOenv :: InternalFuncEnv
              _stmtOfinal :: (S.Set Label)
              _stmtOfresh :: Labels
              _stmtOtest :: Expression
              _testIfolded :: MExpression
              _testIself :: MExpression
              _stepIfolded :: MExpression
              _stepIself :: MExpression
              _stmtIblocks :: (M.Map Label Block)
              _stmtIdesugared :: Statements
              _stmtIenv :: InternalFuncEnv
              _stmtIenvAVars :: EnvAVars
              _stmtIfallthrough :: Statements
              _stmtIfinal :: (S.Set Label)
              _stmtIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmtIfresh :: Labels
              _stmtIinit :: (Maybe Label)
              _stmtIself :: Statement
              _stmtIvars :: AVars
              _lhsOdesugared =
                  ({-# LINE 31 "./src/JS/AG/Desugaring.ag" #-}
                   case init_ of
                          NoInit -> []
                          VarInit vardecls  -> [VarDeclStmt vardecls]
                          ExprInit expr -> [ExprStmt expr]
                   ++
                   [WhileStmt (case _testIself of
                                      NoExpr -> BoolLit True
                                      JustExpr e -> e)
                              (BlockStmt (_stmtIdesugared ++ (case _stepIself of
                                                                        NoExpr -> []
                                                                        JustExpr e -> [ExprStmt e])))]
                   {-# LINE 5218 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _stmtIblocks
                   {-# LINE 5223 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtIenvAVars
                   {-# LINE 5228 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _stmtIfallthrough
                   {-# LINE 5233 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _stmtIfinal
                   {-# LINE 5238 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _stmtIflow
                   {-# LINE 5243 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _stmtIvars
                   {-# LINE 5248 "src/JS/AG.hs" #-}
                   )
              _self =
                  ForStmt init_ _testIself _stepIself _stmtIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _stmtIenv
                   {-# LINE 5257 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _stmtIfresh
                   {-# LINE 5262 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _stmtIinit
                   {-# LINE 5267 "src/JS/AG.hs" #-}
                   )
              _testOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ForStmt.test.analyseData"
                   {-# LINE 5272 "src/JS/AG.hs" #-}
                   )
              _testOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ForStmt.test.currLabel"
                   {-# LINE 5277 "src/JS/AG.hs" #-}
                   )
              _stepOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ForStmt.step.analyseData"
                   {-# LINE 5282 "src/JS/AG.hs" #-}
                   )
              _stepOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ForStmt.step.currLabel"
                   {-# LINE 5287 "src/JS/AG.hs" #-}
                   )
              _stmtOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5292 "src/JS/AG.hs" #-}
                   )
              _stmtOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5297 "src/JS/AG.hs" #-}
                   )
              _stmtOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5302 "src/JS/AG.hs" #-}
                   )
              _stmtOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 5307 "src/JS/AG.hs" #-}
                   )
              _stmtOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 5312 "src/JS/AG.hs" #-}
                   )
              ( _testIfolded,_testIself) =
                  test_ _testOanalyseData _testOcurrLabel
              ( _stepIfolded,_stepIself) =
                  step_ _stepOanalyseData _stepOcurrLabel
              ( _stmtIblocks,_stmtIdesugared,_stmtIenv,_stmtIenvAVars,_stmtIfallthrough,_stmtIfinal,_stmtIflow,_stmtIfresh,_stmtIinit,_stmtIself,_stmtIvars) =
                  stmt_ _stmtOblocks _stmtOenv _stmtOfinal _stmtOfresh _stmtOtest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_SwitchStmt :: T_Expression ->
                            T_CaseClauses ->
                            T_Statement
sem_Statement_SwitchStmt expr_ clauses_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOdesugared :: Statements
              _clausesOtest :: Expression
              _lhsOblocks :: (M.Map Label Block)
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _clausesIdesugared :: Statements
              _clausesIfallthrough :: Statements
              _clausesIself :: CaseClauses
              _lhsOdesugared =
                  ({-# LINE 43 "./src/JS/AG/Desugaring.ag" #-}
                   case _clausesIself of
                     [] -> [ExprStmt _exprIself]
                     _  -> _clausesIdesugared
                   {-# LINE 5368 "src/JS/AG.hs" #-}
                   )
              _clausesOtest =
                  ({-# LINE 46 "./src/JS/AG/Desugaring.ag" #-}
                   _exprIself
                   {-# LINE 5373 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 5378 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars
                   {-# LINE 5383 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _clausesIfallthrough
                   {-# LINE 5388 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _exprIfinal
                   {-# LINE 5393 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _exprIflow
                   {-# LINE 5398 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars
                   {-# LINE 5403 "src/JS/AG.hs" #-}
                   )
              _self =
                  SwitchStmt _exprIself _clausesIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 5412 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _exprIfresh
                   {-# LINE 5417 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _exprIinit
                   {-# LINE 5422 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.SwitchStmt.expr.analyseData"
                   {-# LINE 5427 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.SwitchStmt.expr.assignResultTo"
                   {-# LINE 5432 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5437 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.SwitchStmt.expr.currLabel"
                   {-# LINE 5442 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5447 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5452 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 5457 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
              ( _clausesIdesugared,_clausesIfallthrough,_clausesIself) =
                  clauses_ _clausesOtest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_FunctionStmt :: String ->
                              ([String]) ->
                              T_Statement ->
                              T_Statement
sem_Statement_FunctionStmt name_ params_ stmt_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _stmtOfresh :: Labels
              _stmtOenv :: InternalFuncEnv
              _lhsOenvAVars :: EnvAVars
              _lhsOvars :: AVars
              _lhsOdesugared :: Statements
              _lhsOfallthrough :: Statements
              _lhsOself :: Statement
              _stmtOblocks :: (M.Map Label Block)
              _stmtOfinal :: (S.Set Label)
              _stmtOtest :: Expression
              _stmtIblocks :: (M.Map Label Block)
              _stmtIdesugared :: Statements
              _stmtIenv :: InternalFuncEnv
              _stmtIenvAVars :: EnvAVars
              _stmtIfallthrough :: Statements
              _stmtIfinal :: (S.Set Label)
              _stmtIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _stmtIfresh :: Labels
              _stmtIinit :: (Maybe Label)
              _stmtIself :: Statement
              _stmtIvars :: AVars
              _nLbl =
                  ({-# LINE 133 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 5504 "src/JS/AG.hs" #-}
                   )
              _xLbl =
                  ({-# LINE 134 "./src/JS/AG/Flow.ag" #-}
                   head _stmtIfresh
                   {-# LINE 5509 "src/JS/AG.hs" #-}
                   )
              _env =
                  ({-# LINE 136 "./src/JS/AG/Flow.ag" #-}
                   (name_, (_nLbl    , _xLbl    , params_)) : _lhsIenv
                   {-# LINE 5514 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 138 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 5519 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 139 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 5524 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 140 "./src/JS/AG/Flow.ag" #-}
                   (M.fromList [(_nLbl    , Function _nLbl     name_ params_), (_xLbl    , End _xLbl    )]) `M.union` _stmtIblocks
                   {-# LINE 5529 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 141 "./src/JS/AG/Flow.ag" #-}
                   case _stmtIinit of
                     Nothing   -> S.singleton (_nLbl     |-> _xLbl    )
                     Just init -> (S.singleton (_nLbl     |-> (fromJust _stmtIinit))) `S.union`
                                  _stmtIflow `S.union`
                                  S.map (\final -> final |-> _xLbl    ) _stmtIfinal
                   {-# LINE 5538 "src/JS/AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 148 "./src/JS/AG/Flow.ag" #-}
                   _env     ++ _stmtIenv
                   {-# LINE 5543 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 150 "./src/JS/AG/Flow.ag" #-}
                   tail _stmtIfresh
                   {-# LINE 5548 "src/JS/AG.hs" #-}
                   )
              _stmtOfresh =
                  ({-# LINE 152 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 5553 "src/JS/AG.hs" #-}
                   )
              _stmtOenv =
                  ({-# LINE 153 "./src/JS/AG/Flow.ag" #-}
                   _env
                   {-# LINE 5558 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 12 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.singleton name_ ((S.fromList params_) `S.union` _stmtIvars)
                   {-# LINE 5563 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 13 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 5568 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 30 "./src/JS/AG/Desugaring.ag" #-}
                   [FunctionStmt name_ params_ (BlockStmt _stmtIdesugared)]
                   {-# LINE 5573 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   _stmtIfallthrough
                   {-# LINE 5578 "src/JS/AG.hs" #-}
                   )
              _self =
                  FunctionStmt name_ params_ _stmtIself
              _lhsOself =
                  _self
              _stmtOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5587 "src/JS/AG.hs" #-}
                   )
              _stmtOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5592 "src/JS/AG.hs" #-}
                   )
              _stmtOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   _lhsItest
                   {-# LINE 5597 "src/JS/AG.hs" #-}
                   )
              ( _stmtIblocks,_stmtIdesugared,_stmtIenv,_stmtIenvAVars,_stmtIfallthrough,_stmtIfinal,_stmtIflow,_stmtIfresh,_stmtIinit,_stmtIself,_stmtIvars) =
                  stmt_ _stmtOblocks _stmtOenv _stmtOfinal _stmtOfresh _stmtOtest
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_ReturnStmt :: T_MExpression ->
                            T_Statement
sem_Statement_ReturnStmt expr_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOcurrLabel :: Int
              _exprIfolded :: MExpression
              _exprIself :: MExpression
              _lbl =
                  ({-# LINE 156 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 5628 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 158 "./src/JS/AG/Flow.ag" #-}
                   Just _lbl
                   {-# LINE 5633 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 159 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _lbl
                   {-# LINE 5638 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 160 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _lbl     (Return _lbl     _exprIself)
                   {-# LINE 5643 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 161 "./src/JS/AG/Flow.ag" #-}
                   let (_, (_, exit, _)) = head _lhsIenv
                   in S.singleton (_lbl     |-> exit)
                   {-# LINE 5649 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 164 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 5654 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 24 "./src/JS/AG/Desugaring.ag" #-}
                   [_self]
                   {-# LINE 5659 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 5664 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 5669 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 5674 "src/JS/AG.hs" #-}
                   )
              _self =
                  ReturnStmt _exprIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5683 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ReturnStmt.expr.analyseData"
                   {-# LINE 5688 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ReturnStmt.expr.currLabel"
                   {-# LINE 5693 "src/JS/AG.hs" #-}
                   )
              ( _exprIfolded,_exprIself) =
                  expr_ _exprOanalyseData _exprOcurrLabel
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statement_ParamStmt :: String ->
                           T_Expression ->
                           T_Statement
sem_Statement_ParamStmt name_ expr_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh
       _lhsItest ->
         (let _lhsOblocks :: (M.Map Label Block)
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOfallthrough :: Statements
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statement
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit :: (Maybe Label)
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _exprIblocks
                   {-# LINE 5739 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 5 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 5744 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIenvAVars
                   {-# LINE 5749 "src/JS/AG.hs" #-}
                   )
              _lhsOfallthrough =
                  ({-# LINE 8 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 5754 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 28 "./src/JS/AG/Flow.ag" #-}
                   _exprIfinal
                   {-# LINE 5759 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   _exprIflow
                   {-# LINE 5764 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _exprIvars
                   {-# LINE 5769 "src/JS/AG.hs" #-}
                   )
              _self =
                  ParamStmt name_ _exprIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 5778 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _exprIfresh
                   {-# LINE 5783 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 26 "./src/JS/AG/Flow.ag" #-}
                   _exprIinit
                   {-# LINE 5788 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 8 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ParamStmt.expr.analyseData"
                   {-# LINE 5793 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: Statement.ParamStmt.expr.assignResultTo"
                   {-# LINE 5798 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5803 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   error "missing rule: Statement.ParamStmt.expr.currLabel"
                   {-# LINE 5808 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5813 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5818 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 5823 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfallthrough,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
-- Statements --------------------------------------------------
type Statements = [Statement]
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list))
-- semantic domain
type T_Statements = (M.Map Label Block) ->
                    InternalFuncEnv ->
                    (S.Set Label) ->
                    Labels ->
                    ( (M.Map Label Block),Statements,InternalFuncEnv,EnvAVars,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),Labels,(Maybe Label),Statements,AVars)
data Inh_Statements = Inh_Statements {blocks_Inh_Statements :: (M.Map Label Block),env_Inh_Statements :: InternalFuncEnv,final_Inh_Statements :: (S.Set Label),fresh_Inh_Statements :: Labels}
data Syn_Statements = Syn_Statements {blocks_Syn_Statements :: (M.Map Label Block),desugared_Syn_Statements :: Statements,env_Syn_Statements :: InternalFuncEnv,envAVars_Syn_Statements :: EnvAVars,final_Syn_Statements :: (S.Set Label),flow_Syn_Statements :: (S.Set (Either FlowEdge InterFlowEntry)),fresh_Syn_Statements :: Labels,init_Syn_Statements :: (Maybe Label),self_Syn_Statements :: Statements,vars_Syn_Statements :: AVars}
wrap_Statements :: T_Statements ->
                   Inh_Statements ->
                   Syn_Statements
wrap_Statements sem (Inh_Statements _lhsIblocks _lhsIenv _lhsIfinal _lhsIfresh) =
    (let ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars) = sem _lhsIblocks _lhsIenv _lhsIfinal _lhsIfresh
     in  (Syn_Statements _lhsOblocks _lhsOdesugared _lhsOenv _lhsOenvAVars _lhsOfinal _lhsOflow _lhsOfresh _lhsOinit _lhsOself _lhsOvars))
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_ =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOenv :: InternalFuncEnv
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _tlOfinal :: (S.Set Label)
              _tlOenv :: InternalFuncEnv
              _lhsOblocks :: (M.Map Label Block)
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOvars :: AVars
              _lhsOself :: Statements
              _lhsOfresh :: Labels
              _hdOblocks :: (M.Map Label Block)
              _hdOenv :: InternalFuncEnv
              _hdOfinal :: (S.Set Label)
              _hdOfresh :: Labels
              _hdOtest :: Expression
              _tlOblocks :: (M.Map Label Block)
              _tlOfresh :: Labels
              _hdIblocks :: (M.Map Label Block)
              _hdIdesugared :: Statements
              _hdIenv :: InternalFuncEnv
              _hdIenvAVars :: EnvAVars
              _hdIfallthrough :: Statements
              _hdIfinal :: (S.Set Label)
              _hdIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _hdIfresh :: Labels
              _hdIinit :: (Maybe Label)
              _hdIself :: Statement
              _hdIvars :: AVars
              _tlIblocks :: (M.Map Label Block)
              _tlIdesugared :: Statements
              _tlIenv :: InternalFuncEnv
              _tlIenvAVars :: EnvAVars
              _tlIfinal :: (S.Set Label)
              _tlIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _tlIfresh :: Labels
              _tlIinit :: (Maybe Label)
              _tlIself :: Statements
              _tlIvars :: AVars
              _lhsOinit =
                  ({-# LINE 75 "./src/JS/AG/Flow.ag" #-}
                   _hdIinit
                   {-# LINE 5900 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 76 "./src/JS/AG/Flow.ag" #-}
                   _tlIfinal
                   {-# LINE 5905 "src/JS/AG.hs" #-}
                   )
              _lhsOenv =
                  ({-# LINE 77 "./src/JS/AG/Flow.ag" #-}
                   _hdIenv ++ _tlIenv
                   {-# LINE 5910 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 78 "./src/JS/AG/Flow.ag" #-}
                   let flow = _hdIflow `S.union` _tlIflow
                   in case _tlIinit of
                       Nothing   -> flow
                       Just init -> flow `S.union` (S.map (\final -> final |-> init) _hdIfinal)
                   {-# LINE 5918 "src/JS/AG.hs" #-}
                   )
              _tlOfinal =
                  ({-# LINE 84 "./src/JS/AG/Flow.ag" #-}
                   _hdIfinal
                   {-# LINE 5923 "src/JS/AG.hs" #-}
                   )
              _tlOenv =
                  ({-# LINE 85 "./src/JS/AG/Flow.ag" #-}
                   _hdIenv
                   {-# LINE 5928 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks `M.union` _tlIblocks
                   {-# LINE 5933 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 5 "./src/JS/AG/Desugaring.ag" #-}
                   _hdIdesugared ++ _tlIdesugared
                   {-# LINE 5938 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   _hdIenvAVars `M.union` _tlIenvAVars
                   {-# LINE 5943 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   _hdIvars `S.union` _tlIvars
                   {-# LINE 5948 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _tlIfresh
                   {-# LINE 5957 "src/JS/AG.hs" #-}
                   )
              _hdOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 5962 "src/JS/AG.hs" #-}
                   )
              _hdOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 5967 "src/JS/AG.hs" #-}
                   )
              _hdOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 5972 "src/JS/AG.hs" #-}
                   )
              _hdOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 5977 "src/JS/AG.hs" #-}
                   )
              _hdOtest =
                  ({-# LINE 9 "./src/JS/AG/Desugaring.ag" #-}
                   error "missing rule: Statements.Cons.hd.test"
                   {-# LINE 5982 "src/JS/AG.hs" #-}
                   )
              _tlOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks
                   {-# LINE 5987 "src/JS/AG.hs" #-}
                   )
              _tlOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _hdIfresh
                   {-# LINE 5992 "src/JS/AG.hs" #-}
                   )
              ( _hdIblocks,_hdIdesugared,_hdIenv,_hdIenvAVars,_hdIfallthrough,_hdIfinal,_hdIflow,_hdIfresh,_hdIinit,_hdIself,_hdIvars) =
                  hd_ _hdOblocks _hdOenv _hdOfinal _hdOfresh _hdOtest
              ( _tlIblocks,_tlIdesugared,_tlIenv,_tlIenvAVars,_tlIfinal,_tlIflow,_tlIfresh,_tlIinit,_tlIself,_tlIvars) =
                  tl_ _tlOblocks _tlOenv _tlOfinal _tlOfresh
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil =
    (\ _lhsIblocks
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOdesugared :: Statements
              _lhsOenvAVars :: EnvAVars
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOvars :: AVars
              _lhsOself :: Statements
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit =
                  ({-# LINE 72 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 6018 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 73 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 6023 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 6028 "src/JS/AG.hs" #-}
                   )
              _lhsOdesugared =
                  ({-# LINE 5 "./src/JS/AG/Desugaring.ag" #-}
                   []
                   {-# LINE 6033 "src/JS/AG.hs" #-}
                   )
              _lhsOenvAVars =
                  ({-# LINE 9 "./src/JS/AG/AvailableVariables.ag" #-}
                   M.empty
                   {-# LINE 6038 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 6043 "src/JS/AG.hs" #-}
                   )
              _lhsOvars =
                  ({-# LINE 8 "./src/JS/AG/AvailableVariables.ag" #-}
                   S.empty
                   {-# LINE 6048 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 6057 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 6062 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOdesugared,_lhsOenv,_lhsOenvAVars,_lhsOfinal,_lhsOflow,_lhsOfresh,_lhsOinit,_lhsOself,_lhsOvars)))
-- UnaryAssignOp -----------------------------------------------
data UnaryAssignOp = PrefixInc
                   | PrefixDec
                   | PostfixInc
                   | PostfixDec
-- cata
sem_UnaryAssignOp :: UnaryAssignOp ->
                     T_UnaryAssignOp
sem_UnaryAssignOp (PrefixInc) =
    (sem_UnaryAssignOp_PrefixInc)
sem_UnaryAssignOp (PrefixDec) =
    (sem_UnaryAssignOp_PrefixDec)
sem_UnaryAssignOp (PostfixInc) =
    (sem_UnaryAssignOp_PostfixInc)
sem_UnaryAssignOp (PostfixDec) =
    (sem_UnaryAssignOp_PostfixDec)
-- semantic domain
type T_UnaryAssignOp = ( UnaryAssignOp)
data Inh_UnaryAssignOp = Inh_UnaryAssignOp {}
data Syn_UnaryAssignOp = Syn_UnaryAssignOp {self_Syn_UnaryAssignOp :: UnaryAssignOp}
wrap_UnaryAssignOp :: T_UnaryAssignOp ->
                      Inh_UnaryAssignOp ->
                      Syn_UnaryAssignOp
wrap_UnaryAssignOp sem (Inh_UnaryAssignOp) =
    (let ( _lhsOself) = sem
     in  (Syn_UnaryAssignOp _lhsOself))
sem_UnaryAssignOp_PrefixInc :: T_UnaryAssignOp
sem_UnaryAssignOp_PrefixInc =
    (let _lhsOself :: UnaryAssignOp
         _self =
             PrefixInc
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_UnaryAssignOp_PrefixDec :: T_UnaryAssignOp
sem_UnaryAssignOp_PrefixDec =
    (let _lhsOself :: UnaryAssignOp
         _self =
             PrefixDec
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_UnaryAssignOp_PostfixInc :: T_UnaryAssignOp
sem_UnaryAssignOp_PostfixInc =
    (let _lhsOself :: UnaryAssignOp
         _self =
             PostfixInc
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_UnaryAssignOp_PostfixDec :: T_UnaryAssignOp
sem_UnaryAssignOp_PostfixDec =
    (let _lhsOself :: UnaryAssignOp
         _self =
             PostfixDec
         _lhsOself =
             _self
     in  ( _lhsOself))
-- VarDecl -----------------------------------------------------
data VarDecl = VarDecl (String)
             | VarDeclExpr (String) (Expression)
-- cata
sem_VarDecl :: VarDecl ->
               T_VarDecl
sem_VarDecl (VarDecl _name) =
    (sem_VarDecl_VarDecl _name)
sem_VarDecl (VarDeclExpr _name _expr) =
    (sem_VarDecl_VarDeclExpr _name (sem_Expression _expr))
-- semantic domain
type T_VarDecl = ([(Int,[Int],String,ZTB)]) ->
                 (M.Map Label Block) ->
                 Int ->
                 InternalFuncEnv ->
                 Labels ->
                 ( (M.Map Label Block),InternalFuncEnv,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),VarDecl,Labels,(Maybe Label),VarDecl)
data Inh_VarDecl = Inh_VarDecl {analyseData_Inh_VarDecl :: ([(Int,[Int],String,ZTB)]),blocks_Inh_VarDecl :: (M.Map Label Block),currLabel_Inh_VarDecl :: Int,env_Inh_VarDecl :: InternalFuncEnv,fresh_Inh_VarDecl :: Labels}
data Syn_VarDecl = Syn_VarDecl {blocks_Syn_VarDecl :: (M.Map Label Block),env_Syn_VarDecl :: InternalFuncEnv,final_Syn_VarDecl :: (S.Set Label),flow_Syn_VarDecl :: (S.Set (Either FlowEdge InterFlowEntry)),folded_Syn_VarDecl :: VarDecl,fresh_Syn_VarDecl :: Labels,init_Syn_VarDecl :: (Maybe Label),self_Syn_VarDecl :: VarDecl}
wrap_VarDecl :: T_VarDecl ->
                Inh_VarDecl ->
                Syn_VarDecl
wrap_VarDecl sem (Inh_VarDecl _lhsIanalyseData _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfresh) =
    (let ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself) = sem _lhsIanalyseData _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfresh
     in  (Syn_VarDecl _lhsOblocks _lhsOenv _lhsOfinal _lhsOflow _lhsOfolded _lhsOfresh _lhsOinit _lhsOself))
sem_VarDecl_VarDecl :: String ->
                       T_VarDecl
sem_VarDecl_VarDecl name_ =
    (\ _lhsIanalyseData
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _lhsOfolded :: VarDecl
              _lhsOself :: VarDecl
              _lhsOenv :: InternalFuncEnv
              _lbl =
                  ({-# LINE 268 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 6167 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 270 "./src/JS/AG/Flow.ag" #-}
                   Just _lbl
                   {-# LINE 6172 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 271 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _lbl
                   {-# LINE 6177 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 272 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _lbl     (Decl _lbl     name_)
                   {-# LINE 6182 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 273 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 6187 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 275 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 6192 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 233 "./src/JS/AG/Folding.ag" #-}
                   _self
                   {-# LINE 6197 "src/JS/AG.hs" #-}
                   )
              _analyseData =
                  ({-# LINE 234 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 6202 "src/JS/AG.hs" #-}
                   )
              _self =
                  VarDecl name_
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 6211 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself)))
sem_VarDecl_VarDeclExpr :: String ->
                           T_Expression ->
                           T_VarDecl
sem_VarDecl_VarDeclExpr name_ expr_ =
    (\ _lhsIanalyseData
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOfresh :: Labels
              _lhsOfolded :: VarDecl
              _exprOanalyseData :: ([(Int,[Int],String,ZTB)])
              _lhsOself :: VarDecl
              _lhsOenv :: InternalFuncEnv
              _exprOassignResultTo :: (Maybe String)
              _exprOblocks :: (M.Map Label Block)
              _exprOcurrLabel :: Int
              _exprOenv :: InternalFuncEnv
              _exprOfinal :: (S.Set Label)
              _exprOfresh :: Labels
              _exprIblocks :: (M.Map Label Block)
              _exprIenv :: InternalFuncEnv
              _exprIenvAVars :: EnvAVars
              _exprIfinal :: (S.Set Label)
              _exprIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _exprIfolded :: Expression
              _exprIfresh :: Labels
              _exprIinit :: (Maybe Label)
              _exprIself :: Expression
              _exprIvalue :: ExprValue
              _exprIvars :: AVars
              _lbl =
                  ({-# LINE 278 "./src/JS/AG/Flow.ag" #-}
                   head _lhsIfresh
                   {-# LINE 6252 "src/JS/AG.hs" #-}
                   )
              _lhsOinit =
                  ({-# LINE 280 "./src/JS/AG/Flow.ag" #-}
                   Just _lbl
                   {-# LINE 6257 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 281 "./src/JS/AG/Flow.ag" #-}
                   S.singleton _lbl
                   {-# LINE 6262 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 282 "./src/JS/AG/Flow.ag" #-}
                   M.singleton _lbl     (Assign _lbl     name_ _exprIself)
                   {-# LINE 6267 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 283 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 6272 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 285 "./src/JS/AG/Flow.ag" #-}
                   tail _lhsIfresh
                   {-# LINE 6277 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 235 "./src/JS/AG/Folding.ag" #-}
                   VarDeclExpr name_ _exprIfolded
                   {-# LINE 6282 "src/JS/AG.hs" #-}
                   )
              _exprOanalyseData =
                  ({-# LINE 236 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 6287 "src/JS/AG.hs" #-}
                   )
              _self =
                  VarDeclExpr name_ _exprIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _exprIenv
                   {-# LINE 6296 "src/JS/AG.hs" #-}
                   )
              _exprOassignResultTo =
                  ({-# LINE 35 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: VarDecl.VarDeclExpr.expr.assignResultTo"
                   {-# LINE 6301 "src/JS/AG.hs" #-}
                   )
              _exprOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 6306 "src/JS/AG.hs" #-}
                   )
              _exprOcurrLabel =
                  ({-# LINE 11 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 6311 "src/JS/AG.hs" #-}
                   )
              _exprOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 6316 "src/JS/AG.hs" #-}
                   )
              _exprOfinal =
                  ({-# LINE 32 "./src/JS/AG/Flow.ag" #-}
                   error "missing rule: VarDecl.VarDeclExpr.expr.final"
                   {-# LINE 6321 "src/JS/AG.hs" #-}
                   )
              _exprOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 6326 "src/JS/AG.hs" #-}
                   )
              ( _exprIblocks,_exprIenv,_exprIenvAVars,_exprIfinal,_exprIflow,_exprIfolded,_exprIfresh,_exprIinit,_exprIself,_exprIvalue,_exprIvars) =
                  expr_ _exprOanalyseData _exprOassignResultTo _exprOblocks _exprOcurrLabel _exprOenv _exprOfinal _exprOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself)))
-- VarDecls ----------------------------------------------------
type VarDecls = [VarDecl]
-- cata
sem_VarDecls :: VarDecls ->
                T_VarDecls
sem_VarDecls list =
    (Prelude.foldr sem_VarDecls_Cons sem_VarDecls_Nil (Prelude.map sem_VarDecl list))
-- semantic domain
type T_VarDecls = ([(Int,[Int],String,ZTB)]) ->
                  (M.Map Label Block) ->
                  Int ->
                  InternalFuncEnv ->
                  (S.Set Label) ->
                  Labels ->
                  ( (M.Map Label Block),InternalFuncEnv,(S.Set Label),(S.Set (Either FlowEdge InterFlowEntry)),VarDecls,Labels,(Maybe Label),VarDecls)
data Inh_VarDecls = Inh_VarDecls {analyseData_Inh_VarDecls :: ([(Int,[Int],String,ZTB)]),blocks_Inh_VarDecls :: (M.Map Label Block),currLabel_Inh_VarDecls :: Int,env_Inh_VarDecls :: InternalFuncEnv,final_Inh_VarDecls :: (S.Set Label),fresh_Inh_VarDecls :: Labels}
data Syn_VarDecls = Syn_VarDecls {blocks_Syn_VarDecls :: (M.Map Label Block),env_Syn_VarDecls :: InternalFuncEnv,final_Syn_VarDecls :: (S.Set Label),flow_Syn_VarDecls :: (S.Set (Either FlowEdge InterFlowEntry)),folded_Syn_VarDecls :: VarDecls,fresh_Syn_VarDecls :: Labels,init_Syn_VarDecls :: (Maybe Label),self_Syn_VarDecls :: VarDecls}
wrap_VarDecls :: T_VarDecls ->
                 Inh_VarDecls ->
                 Syn_VarDecls
wrap_VarDecls sem (Inh_VarDecls _lhsIanalyseData _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh) =
    (let ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself) = sem _lhsIanalyseData _lhsIblocks _lhsIcurrLabel _lhsIenv _lhsIfinal _lhsIfresh
     in  (Syn_VarDecls _lhsOblocks _lhsOenv _lhsOfinal _lhsOflow _lhsOfolded _lhsOfresh _lhsOinit _lhsOself))
sem_VarDecls_Cons :: T_VarDecl ->
                     T_VarDecls ->
                     T_VarDecls
sem_VarDecls_Cons hd_ tl_ =
    (\ _lhsIanalyseData
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _tlOfinal :: (S.Set Label)
              _lhsOfolded :: VarDecls
              _hdOanalyseData :: ([(Int,[Int],String,ZTB)])
              _tlOanalyseData :: ([(Int,[Int],String,ZTB)])
              _hdOcurrLabel :: Int
              _tlOcurrLabel :: Int
              _lhsOblocks :: (M.Map Label Block)
              _lhsOself :: VarDecls
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _hdOblocks :: (M.Map Label Block)
              _hdOenv :: InternalFuncEnv
              _hdOfresh :: Labels
              _tlOblocks :: (M.Map Label Block)
              _tlOenv :: InternalFuncEnv
              _tlOfresh :: Labels
              _hdIblocks :: (M.Map Label Block)
              _hdIenv :: InternalFuncEnv
              _hdIfinal :: (S.Set Label)
              _hdIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _hdIfolded :: VarDecl
              _hdIfresh :: Labels
              _hdIinit :: (Maybe Label)
              _hdIself :: VarDecl
              _tlIblocks :: (M.Map Label Block)
              _tlIenv :: InternalFuncEnv
              _tlIfinal :: (S.Set Label)
              _tlIflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _tlIfolded :: VarDecls
              _tlIfresh :: Labels
              _tlIinit :: (Maybe Label)
              _tlIself :: VarDecls
              _lhsOinit =
                  ({-# LINE 100 "./src/JS/AG/Flow.ag" #-}
                   _hdIinit
                   {-# LINE 6402 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 101 "./src/JS/AG/Flow.ag" #-}
                   _tlIfinal
                   {-# LINE 6407 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 102 "./src/JS/AG/Flow.ag" #-}
                   let flow = _hdIflow `S.union` _tlIflow
                   in case _tlIinit of
                       Nothing   -> flow
                       Just init -> flow `S.union` (S.map (\final -> final |-> init) _hdIfinal)
                   {-# LINE 6415 "src/JS/AG.hs" #-}
                   )
              _tlOfinal =
                  ({-# LINE 108 "./src/JS/AG/Flow.ag" #-}
                   _hdIfinal
                   {-# LINE 6420 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 62 "./src/JS/AG/Folding.ag" #-}
                   _hdIfolded : _tlIfolded
                   {-# LINE 6425 "src/JS/AG.hs" #-}
                   )
              _hdOanalyseData =
                  ({-# LINE 63 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 6430 "src/JS/AG.hs" #-}
                   )
              _tlOanalyseData =
                  ({-# LINE 64 "./src/JS/AG/Folding.ag" #-}
                   _lhsIanalyseData
                   {-# LINE 6435 "src/JS/AG.hs" #-}
                   )
              _hdOcurrLabel =
                  ({-# LINE 65 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 6440 "src/JS/AG.hs" #-}
                   )
              _tlOcurrLabel =
                  ({-# LINE 66 "./src/JS/AG/Folding.ag" #-}
                   _lhsIcurrLabel
                   {-# LINE 6445 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks `M.union` _tlIblocks
                   {-# LINE 6450 "src/JS/AG.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _tlIenv
                   {-# LINE 6459 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _tlIfresh
                   {-# LINE 6464 "src/JS/AG.hs" #-}
                   )
              _hdOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _lhsIblocks
                   {-# LINE 6469 "src/JS/AG.hs" #-}
                   )
              _hdOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 6474 "src/JS/AG.hs" #-}
                   )
              _hdOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 6479 "src/JS/AG.hs" #-}
                   )
              _tlOblocks =
                  ({-# LINE 23 "./src/JS/AG/Flow.ag" #-}
                   _hdIblocks
                   {-# LINE 6484 "src/JS/AG.hs" #-}
                   )
              _tlOenv =
                  ({-# LINE 22 "./src/JS/AG/Flow.ag" #-}
                   _hdIenv
                   {-# LINE 6489 "src/JS/AG.hs" #-}
                   )
              _tlOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _hdIfresh
                   {-# LINE 6494 "src/JS/AG.hs" #-}
                   )
              ( _hdIblocks,_hdIenv,_hdIfinal,_hdIflow,_hdIfolded,_hdIfresh,_hdIinit,_hdIself) =
                  hd_ _hdOanalyseData _hdOblocks _hdOcurrLabel _hdOenv _hdOfresh
              ( _tlIblocks,_tlIenv,_tlIfinal,_tlIflow,_tlIfolded,_tlIfresh,_tlIinit,_tlIself) =
                  tl_ _tlOanalyseData _tlOblocks _tlOcurrLabel _tlOenv _tlOfinal _tlOfresh
          in  ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself)))
sem_VarDecls_Nil :: T_VarDecls
sem_VarDecls_Nil =
    (\ _lhsIanalyseData
       _lhsIblocks
       _lhsIcurrLabel
       _lhsIenv
       _lhsIfinal
       _lhsIfresh ->
         (let _lhsOinit :: (Maybe Label)
              _lhsOfinal :: (S.Set Label)
              _lhsOfolded :: VarDecls
              _lhsOblocks :: (M.Map Label Block)
              _lhsOflow :: (S.Set (Either FlowEdge InterFlowEntry))
              _lhsOself :: VarDecls
              _lhsOenv :: InternalFuncEnv
              _lhsOfresh :: Labels
              _lhsOinit =
                  ({-# LINE 97 "./src/JS/AG/Flow.ag" #-}
                   Nothing
                   {-# LINE 6520 "src/JS/AG.hs" #-}
                   )
              _lhsOfinal =
                  ({-# LINE 98 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfinal
                   {-# LINE 6525 "src/JS/AG.hs" #-}
                   )
              _lhsOfolded =
                  ({-# LINE 61 "./src/JS/AG/Folding.ag" #-}
                   []
                   {-# LINE 6530 "src/JS/AG.hs" #-}
                   )
              _lhsOblocks =
                  ({-# LINE 29 "./src/JS/AG/Flow.ag" #-}
                   M.empty
                   {-# LINE 6535 "src/JS/AG.hs" #-}
                   )
              _lhsOflow =
                  ({-# LINE 27 "./src/JS/AG/Flow.ag" #-}
                   S.empty
                   {-# LINE 6540 "src/JS/AG.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOenv =
                  ({-# LINE 25 "./src/JS/AG/Flow.ag" #-}
                   _lhsIenv
                   {-# LINE 6549 "src/JS/AG.hs" #-}
                   )
              _lhsOfresh =
                  ({-# LINE 20 "./src/JS/AG/Flow.ag" #-}
                   _lhsIfresh
                   {-# LINE 6554 "src/JS/AG.hs" #-}
                   )
          in  ( _lhsOblocks,_lhsOenv,_lhsOfinal,_lhsOflow,_lhsOfolded,_lhsOfresh,_lhsOinit,_lhsOself)))