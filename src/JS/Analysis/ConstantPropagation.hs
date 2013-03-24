module JS.Analysis.ConstantPropagation where
import Monotone.Interface
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Query.DFS as G
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Data.Monoid
import Data.Maybe (fromJust)
import JS.AG
import JS.Analysis.CP.Base
import Debug.Trace

-- The 'constantPropagation' function creates an instance of a embellished monotone framework
-- for constant propagation when passed an extremal label, an environment that contains information about the
-- available functions, a mapping from function names to the available variables, and the flow graph.
--
-- Todo: merge FuncEnv and (String -> AVars) there no reason why they should be separate
--
-- The ECMA-262 script standard of which Javascript is an implementation
-- http://www.ecma-international.org/publications/files/ECMA-ST-ARCH/ECMA-262,%203rd%20edition,%20December%201999.pdf
--
-- The following restrictions apply:
--  - only local scoping
--  - only supports numerical constant propagation
--  - context is represented by unbounded callstrings, i.e. no support for recursive methods
--
-- Restrictions on Javascript:
--  - the left handside of an assignment cannot be an expression
--  - functions should have unique names
--  - no nested, recursive, anonymous, and mutually recursive functions
--  - no objects, thus also no foreach
--  - no scoping
--  - function calls cannot appear as part of an expression that itself contains other expressions, with 
--    as exception the assignment expression wherein a function call can be placed on the rhs, e.g. z=f();
--  - there is no notion of references  
--  - function parameters can only be constants or expressions that do not contain function calls
--  - return expressions cannot contain function calls
--  - the number of arguments to a function call must correspond with the number of formal parameters
--    in the function definition
--  - ...
--  - probably missed something
constantPropagation :: G.Graph gr => 
  ExtremalLabel -> 
  FuncEnv -> 
  (String -> AVars) -> 
  FlowGraph gr Block -> 
  MonotoneFramework gr [Int] Block ConstantProp
constantPropagation lbl funcEnv avars graph@(intra,inter) = 
  let extremalLabel = lbl

      extremalValue = let allUndefined = map (\x -> (x,Bottom)) (S.toList $ avars "")
                      in CP (M.fromList allUndefined)

      lookupFunc f = fromJust $ M.lookup f funcEnv

      transferFunctionSpace lbl =
        case lookup lbl (G.labNodes intra) of
          Just b@(Assign _ _ _)             -> Left $ liftUnary (tfAssign b)
          Just b@(Call _ _ f _)             -> Left $ tfCall' b (lookupFunc f) (avars f)
          Just b@(Function _ _ _)           -> Left $ liftUnary id
          Just b@(ReturnFromCall _ _ _ _ _) -> Right $ tfReturnCall' b
          Just b@(Return _ _)               -> Left $ liftUnary (tfReturn b)
          Just b@(While _ _)                -> Left $ liftUnary id
          Just b@(End _)                    -> Left $ liftUnary tfExit 
          Just b@(Skip _)                   -> Left $ liftUnary id
          Just b@(Decl _ _)                 -> Left $ liftUnary id
          Just b@(If _ _)                   -> Left $ liftUnary id
          Nothing                           -> error "empty space, only astronauts present"
      
      flowGraph = graph

      -- no idea why I don't use, lbl : ctx, here...
      mutateContext lbl ctx = [lbl] `mappend` ctx
  in
  MF (extremalLabel, extremalValue, transferFunctionSpace, flowGraph, mutateContext)

-- | The function 'tfAssign' transfers assignment blocks.
tfAssign :: Block -> ConstantProp -> ConstantProp
tfAssign (Assign lbl x expr) cp | M.null (lat cp) = cp
                                | otherwise       = CP $ M.insert x (eval expr cp) (lat cp)
tfAssign _ _ = error "expected assignment, got something else"

-- | The function 'tfCall\'' transfers call blocks.
tfCall' :: Block -> (Label,Label,[String]) -> AVars -> CtxSenUnaryTransfer [Int] ConstantProp
tfCall' (Call _ _ name params) (_,_,formalParams) avars l ctx = 
  let 
      -- Create a assoc list that maps all variables in local scope to bottom, this includes the formal function parameters.
      avarsAndParams = map (\x -> (x,Bottom)) (L.union (S.toList avars) formalParams)

      -- extend the list with the return value holder and create a CP lattice
      -- out of it. By default the return value is undefined, unless it is modified somewhere else by using
      -- the explicit return statement.
      l' = CP $ M.fromList $ (returnName, Bottom) : avarsAndParams

      -- Create another lattice mapping all formal parameters to their
      -- corresponding abstract representation in the ZTB lattice. 
      -- Note that the number of formal parameters must correspond with
      -- the number of call parameters.
      l'' = CP $ M.fromList $ 
              map (\(expr,var) -> (var, eval expr (l ctx))) 
                  (zip params formalParams)

      -- join the two lattices such that the abstract values of the parameters passed into
      -- the function are made consistent with the variables available in the local function scope.
      l''' = l' `join` l''
  in tfCall l'''

-- | The function 'tfCall' does nothing
tfCall :: CtxInsUnaryTransfer ConstantProp
tfCall = id

-- | The function 'tfExit' does nothing
tfExit :: CtxInsUnaryTransfer ConstantProp
tfExit = id 

-- | The function 'tfReturn' transfers return statements. It is similar 
--   to 'tfAssign' except that the assignee is the magical 'returnName'.
--   If the return lacks an accompanying expression it leaves the 
--   return value undefined.
tfReturn :: Block -> CtxInsUnaryTransfer ConstantProp
tfReturn (Return _ NoExpr)     l         = l
tfReturn (Return _ (JustExpr expr)) cp@(CP l) =
  case M.lookup returnName l of
    Nothing -> error "this should not happen, the magic return variable should always be present"
    Just _  -> CP $ M.insert returnName (eval expr cp) l

tfReturn _  l = l

-- | The function 'tfReturnCall' transfers the result of a function call to just after the 
--   call. 
tfReturnCall' :: Block -> CtxSenBinaryTransfer [Int] ConstantProp
tfReturnCall' (ReturnFromCall cLbl _ _ _ result) beforeCall beforeReturn ctx = 
  tfReturnCall result (beforeCall ctx) (beforeReturn (cLbl : ctx))

-- | The function 'tfReturnCall' returns the result of a function call back to the
--   assignee.
tfReturnCall :: Maybe Result -> CtxInsBinaryTransfer ConstantProp
tfReturnCall Nothing  l _       = l
tfReturnCall (Just r) l (CP l') = 
  case M.lookup returnName l' of
    Nothing     -> error "this should not happen, the magic return variable should always be present"
    Just retVal -> l `join` (CP $ M.singleton r retVal)

-- | The 'eval' function evaluates an expression given the constant propagation lattice
--   and returns the abstract representation of evaluation result.
eval :: Expression -> ConstantProp -> ZTB 
eval (IntLit val)               cp = Z val
eval (VarRef x)                 cp = case M.lookup x (lat cp) of 
                                      Nothing  -> error ("variable " ++ x ++ " not found")
                                      Just val -> val
eval (InfixExpr op expr1 expr2) cp = eval expr1 cp `binOp` eval expr2 cp
  where
  binOp = binaryOperator op

binaryOperator OpAdd (Z i)  (Z i')  = Z (i + i')
binaryOperator OpMul (Z i)  (Z i')  = Z (i * i')
binaryOperator OpSub (Z i)  (Z i')  = Z (i - i')

--undefined stays undefined
binaryOperator _     Bottom _       = Bottom
binaryOperator _     _      Bottom  = Bottom

-- everything else stays top
binaryOperator _     _      _       = Top

cpFlatten :: Ord ctx => MFP ctx ConstantProp -> ([(Label,ctx,Var,ZTB)],[(Label,ctx,Var,ZTB)])
cpFlatten cp = 
  let (c,e)       = flatten cp
      f (l,ctx,c) = let xs = M.toList (lat c)
                    in ([(l,ctx,v,ztb) | (v,ztb) <- xs] ++)
  in (foldr f [] c, foldr f [] e)

-- | Returns a magical identifier that is used to track return results, it is important
--   that it does not collide with existing variable definitions and should therefore preferably
--   use characters that are not valid in Javascript as part of an identifier. 
returnName = "__return__"

-- We define 'ConstantProp' to be an instance of 'Lattice'. 
-- Lattices defined on functions as found in the literature are encoded
-- using Data.Map since we need access to all values in the domain and range.
--
-- The constant propagation lattice is defined as a mapping from all
-- program variables to an abstract representation of their value (ZTB) 
-- which by itself is also a lattice.
--
-- Note: Although top is not defined below there really is a top value. 
--       Namely, top is the set of mappings where all variables in the program (which we know to be a finite number)
--       are mapped to Top.
instance Lattice ConstantProp where
  top    = error "no explicit top, top is set union closed by the available variables in P"
  bottom = CP M.empty

  join cp cp' = CP $ M.unionWith join (lat cp) (lat cp')


-- We define 'ZTB' to be an instance of 'Lattice'. 
--
--  Bottom: undefined variables
--  Top:    more than one value
--  Z:      exactly one value
instance Lattice ZTB where
  bottom = Bottom
  top = Top

  join Top    _                  = Top
  join _      Top                = Top
  join Bottom x                  = x
  join x      Bottom             = x
  join (Z i)  (Z i') | i == i'   = Z i
                     | otherwise = Top

instance Ord ConstantProp where
  compare x y | x `join` y == y = LT
              | x == y          = EQ
              | otherwise       = GT  

instance Ord ZTB where
  compare x y | x `join` y == y = LT
              | x == y          = EQ
              | otherwise       = GT


-- Show instance, for convenience
instance Show ConstantProp where
  show (CP m) = M.foldrWithKey f "" m
    where
    f k a "" = k ++ " -> " ++ (show a)
    f k a result = k ++ " -> " ++ (show a) ++ ", " ++ result

