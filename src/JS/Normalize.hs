module JS.Normalize (
   normalize
  ,mapToSubset
) where
import JS.AG
import qualified BrownPLT.JavaScript.Syntax as B
import BrownPLT.JavaScript.Parser
import Text.ParserCombinators.Parsec
import Data.Maybe (maybe)

-- todo: implement normalization
normalize = id

mapToSubset :: B.JavaScript SourcePos -> JavaScript
mapToSubset (B.Script _ stms) = Script (map tStmt stms)
  where
  tStmt (B.BlockStmt _ stms)                 = BlockStmt (map tStmt stms)
  tStmt (B.EmptyStmt _)                      = EmptyStmt 
  tStmt (B.BreakStmt _ b)                    = BreakStmt (maybe Nothing (\(B.Id _ lbl) -> Just lbl) b)
  tStmt (B.ContinueStmt _ b)                 = ContinueStmt (maybe Nothing (\(B.Id _ lbl) -> Just lbl) b)
  tStmt (B.ExprStmt _ expr)                  = ExprStmt (tExpr expr)
  tStmt (B.VarDeclStmt _ decls)              = VarDeclStmt (map tVarDecl decls)
  tStmt (B.IfStmt _ expr stmt1 stmt2)        = IfStmt (tExpr expr) (tStmt stmt1) (tStmt stmt2)
  tStmt (B.WhileStmt _ expr stmt)            = WhileStmt (tExpr expr) (tStmt stmt)
  tStmt (B.FunctionStmt _ (B.Id _ n) p stmt) = FunctionStmt n (map (\(B.Id _ x) -> x) p) (tStmt stmt)
  tStmt (B.ReturnStmt _ expr)                = ReturnStmt (maybe NoExpr (JustExpr . tExpr) expr)
  tStmt (B.LabelledStmt _ b stmt)            = LabelledStmt ((\(B.Id _ lbl) -> Just lbl) b) (tStmt stmt)
  tStmt (B.SwitchStmt _ expr cases)          = SwitchStmt (tExpr expr) (map normalizeSwitchCase cases)
  tStmt (B.ForStmt _ init test step stmt)    = ForStmt 
                                               (case init of B.NoInit -> NoInit; B.VarInit decls -> VarInit (map tVarDecl decls); B.ExprInit expr -> ExprInit (tExpr expr))
                                               (maybe NoExpr (JustExpr . tExpr) test) 
                                               (maybe NoExpr (JustExpr . tExpr) step) 
                                               (tStmt stmt)
  tStmt x                                    = error ((show x) ++ " not supported")

  tExpr (B.StringLit _ val)              = StringLit val
  tExpr (B.NumLit _ val)                 = NumLit val
  tExpr (B.IntLit _ val)                 = IntLit val
  tExpr (B.BoolLit _ val)                = BoolLit val
  tExpr (B.NullLit _)                    = NullLit 
  tExpr (B.VarRef _ (B.Id _ lbl))        = VarRef lbl
  tExpr (B.AssignExpr _ B.OpAssign (B.LVar _ val) r) = AssignExpr val (tExpr r) 
  tExpr (B.ParenExpr _ expr)             = tExpr expr
  tExpr (B.ListExpr _ exprs)             = case exprs of
                                            []  -> ListExpr []
                                            [x] -> tExpr x
                                            xs  -> ListExpr (map tExpr exprs)
  tExpr (B.CondExpr _ expr1 expr2 expr3) = CondExpr (tExpr expr1) (tExpr expr2) (tExpr expr3)
  tExpr (B.InfixExpr _ op expr1 expr2)   = InfixExpr (tInfixOp op) (tExpr expr1) (tExpr expr2)
  tExpr (B.UnaryAssignExpr _ op val)     = UnaryAssignExpr (tUnaryAssignOp op) (tLVal val)
  tExpr (B.PrefixExpr _ op expr)         = PrefixExpr (tPrefixOp op) (tExpr expr)
  tExpr (B.CallExpr _ expr exprs)        = let (VarRef name) = tExpr expr 
                                           in CallExpr name (map tExpr exprs)
  tExpr x                                = error ((show x) ++ " not supported")

  tVarDecl (B.VarDecl _ (B.Id _ lbl) mexpr) = case mexpr of
                                                Nothing -> VarDecl lbl
                                                Just x  -> VarDeclExpr lbl (tExpr x)

  tOp B.OpAssign          = OpAssign
  tOp B.OpAssignAdd       = OpAssignAdd
  tOp B.OpAssignSub       = OpAssignSub
  tOp B.OpAssignMul       = OpAssignMul
  tOp B.OpAssignDiv       = OpAssignDiv
  tOp B.OpAssignMod       = OpAssignMod
  tOp B.OpAssignLShift    = OpAssignLShift
  tOp B.OpAssignSpRShift  = OpAssignSpRShift 
  tOp B.OpAssignZfRShift  = OpAssignZfRShift
  tOp B.OpAssignBAnd      = OpAssignBAnd
  tOp B.OpAssignBXor      = OpAssignBXor
  tOp B.OpAssignBOr       = OpAssignBOr

  tInfixOp B.OpLT         = OpLT
  tInfixOp B.OpLEq        = OpLEq
  tInfixOp B.OpGT         = OpGT
  tInfixOp B.OpGEq        = OpGEq
  tInfixOp B.OpEq         = OpEq
  tInfixOp B.OpNEq        = OpNEq
  tInfixOp B.OpStrictEq   = OpStrictEq
  tInfixOp B.OpStrictNEq  = OpStrictNEq
  tInfixOp B.OpLAnd       = OpLAnd
  tInfixOp B.OpLOr        = OpLOr
  tInfixOp B.OpMul        = OpMul
  tInfixOp B.OpDiv        = OpDiv
  tInfixOp B.OpMod        = OpMod
  tInfixOp B.OpSub        = OpSub
  tInfixOp B.OpLShift     = OpLShift
  tInfixOp B.OpSpRShift   = OpSpRShift
  tInfixOp B.OpZfRShift   = OpZfRShift
  tInfixOp B.OpBAnd       = OpBAnd
  tInfixOp B.OpBXor       = OpBXor
  tInfixOp B.OpBOr        = OpBOr
  tInfixOp B.OpAdd        = OpAdd

  tPrefixOp B.PrefixLNot  = PrefixLNot
  tPrefixOp B.PrefixBNot  = PrefixBNot
  tPrefixOp B.PrefixPlus  = PrefixPlus
  tPrefixOp B.PrefixMinus = PrefixMinus

  tUnaryAssignOp B.PrefixInc  = PrefixInc
  tUnaryAssignOp B.PrefixDec  = PrefixDec
  tUnaryAssignOp B.PostfixInc = PostfixInc
  tUnaryAssignOp B.PostfixDec = PostfixDec

  tLVal (B.LVar _ val) = LVar val
  tLVal x              = error ((show x) ++ " not supported")


  normalizeSwitchCase (B.CaseClause _ expr stmts) = CaseClause (tExpr expr) (map tStmt stmts)
  normalizeSwitchCase (B.CaseDefault _ stmts) = CaseDefault (map tStmt stmts)
