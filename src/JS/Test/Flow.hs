module JS.Test.Flow where
import Test.HUnit 
import Data.Graph.Inductive.Graph
import Monotone.Interface
import Components
import qualified Data.Map as M

-- helpers
edges' intra = M.fromList $ edges intra
set = M.fromList
intraE = edges' . fst . uptoControlFlow
inter = snd . uptoControlFlow

cfgTests = TestList (intraTests ++ interTests)

intraTests = 
  concat [ primExpr
         , primDecl
         , primWhile
         , primIfElse
--         , primBreak
--         , ctxBreak
         , ctxWhile
         , compWhile
         , ctxIfElse
--         , compBreak
         , compWhile
--         , labContinue
--         , continue
--         , labBreak
         ]

interTests = 
  concat [ primFunc 
         , primReturn
         , compFunc
         , paramFunc
         ]

primExpr = 
  [ "x=0;" ~: (set [(1,0),(0,2)]) ~=? (intraE "x=0;")
  , "x=0;x=1;" ~: (set [(0,1),(2,0),(1,3)]) ~=? (intraE "x=0;x=1;")
  ]

primDecl = 
  [ "var x;" ~: (set [(1,0),(0,2)]) ~=? (intraE "var x;")
  , "var x; var y;" ~: (set [(0,1),(2,0),(1,3)]) ~=? (intraE "var x; var y;")
  , "var x, y;" ~: (set [(0,1),(2,0),(1,3)]) ~=? (intraE "var x, y;")
  ]

primWhile = 
  [ "while(true){}" ~: (set [(0,0),(1,0),(0,2)]) ~=? (intraE "while(true){}") 
  , "while(true){z=0;}" ~: (set [(0,1),(1,0),(2,0),(0,3)]) ~=? (intraE "while(true){z=0;}")
  , "while(true){z=0;z=1;}" ~: (set [(0,1),(1,2),(2,0),(3,0),(0,4)]) ~=? (intraE "while(true){z=0;z=1;}")
  ]

primIfElse =
  [ "if(true){}else{}" ~: (set [(1,0),(0,2)]) ~=? (intraE "if(true){}else{}")
  , "if(true){x=0;}else{}" ~: (set [(0,1),(2,0),(0,3),(1,3)]) ~=? (intraE "if(true){z=0;}else{}") 
  , "if(true){}else{x=0;}" ~: (set [(0,1),(2,0),(0,3),(1,3)]) ~=? (intraE "if(true){}else{x=0;}")
  , "if(true){x=0;}else{x=0;}" ~: (set [(0,1),(0,2),(3,0),(1,4),(2,4)]) ~=? (intraE "if(true){x=0;}else{x=0;}")
  , "if(true){x=0;x=0;}else{x=0;}" ~: (set [(0,1),(0,3),(1,2),(4,0),(2,5),(3,5)]) ~=? (intraE "if(true){x=0;x=0;}else{x=0;}")
  , "if(true){x=0;}else{x=0;x=0;}" ~: (set [(0,1),(0,2),(2,3),(4,0),(3,5),(1,5)]) ~=? (intraE "if(true){x=0;}else{x=0;x=0;}")
  , "if(true){x=0;x=0;}else{x=0;x=0;}" ~: (set [(0,1),(0,3),(1,2),(3,4),(5,0),(2,6),(4,6)]) ~=? (intraE "if(true){x=0;x=0;}else{x=0;x=0;}")
  ]

primBreak =
  [ "while(true){break;}" ~: (set [(0,1),(2,0)]) ~=? (intraE "while(true){break;}")
  , "while(true){z=0;break;}" ~: (set [(0,1),(1,2),(3,0)]) ~=? (intraE "while(true){z=0;break;}")
  , "while(true){break;z=0;}" ~: (set [(0,1),(3,0)]) ~=? (intraE "while(true){break;z=0;}")
  ]

ctxBreak =
  [ "while(true){break;}x=0;" ~: (set [(0,1),(0,2),(1,2),(3,0)]) ~=? (intraE "while(true){break;}x=0;")
  , "while(true){x=0;break;}x=0;" ~: (set [(0,1),(0,3),(1,2),(2,3),(4,0)]) ~=? (intraE "while(true){x=0;break;}x=0;")
  , "while(true){break;x=0;}x=0;" ~: (set [(0,1),(0,3),(1,3),(4,0)]) ~=? (intraE "while(true){break;x=0;}x=0;")
  ]

compBreak =
  [ "while(true){if(true){break;}else{break;}}" 
    ~: (set [(0,1),(1,2),(1,3),(4,0)]) 
    ~=? (intraE "while(true){if(true){break;}else{break;}}")

  , "while(true){if(true){break;x=0;}else{break;x=0;}}" 
    ~: (set [(0,1),(1,2),(1,4),(6,0)]) 
    ~=? (intraE "while(true){if(true){break;x=0;}else{break;x=0;}}")

  , "while(true){if(true){break;}else{break;}x=0;}x=0;" 
    ~: (set [(0,1),(0,5),(1,2),(1,3),(2,5),(3,5),(6,0)]) 
    ~=? (intraE "while(true){if(true){break;}else{break;}x=0;}x=0;")

  , "while(true){if(true){x=0;}else{break;x=0;}x=0;}x=0;" 
    ~: (set [(0,1),(0,6),(1,2),(1,3),(2,5),(3,6),(5,0),(7,0)]) 
    ~=? (intraE "while(true){if(true){x=0;}else{break;x=0;}x=0;}x=0;")
  ]

ctxIfElse = 
  [ "x=0;if(true){}else{}" ~: (set [(0,1),(2,0),(1,3)]) ~=? (intraE "x=0;if(true){}else{}")
  , "if(true){}else{}x=0;" ~: (set [(0,1),(2,0),(1,3)]) ~=? (intraE "if(true){}else{}x=0;")
  , "x=0;if(true){}else{}x=0;" ~: (set [(0,1),(1,2),(3,0),(2,4)]) ~=? (intraE "x=0;if(true){}else{}x=0;")

  , "x=0;if(true){x=0;}else{}" ~: (set [(0,1),(1,2),(3,0),(2,4),(1,4)]) ~=? (intraE "x=0;if(true){x=0;}else{}")
  , "if(true){x=0;}else{}x=0;" ~: (set [(0,1),(0,2),(1,2),(3,0),(2,4)]) ~=? (intraE "if(true){x=0;}else{}x=0;")
  , "x=0;if(true){x=0;}else{}x=0;" ~: (set [(0,1),(1,2),(1,3),(2,3),(4,0),(3,5)]) ~=? (intraE "x=0;if(true){x=0;}else{}x=0;")

  , "x=0;if(true){x=0;}else{x=0;}" ~: (set [(0,1),(1,2),(1,3),(4,0),(2,5),(3,5)]) ~=? (intraE "x=0;if(true){x=0;}else{x=0;}")
  , "if(true){x=0;}else{x=0;}x=0;" ~: (set [(0,1),(0,2),(1,3),(2,3),(4,0),(3,5)]) ~=? (intraE "if(true){x=0;}else{x=0;}x=0;")
  , "x=0;if(true){x=0;}else{x=0;}x=0;" ~: (set [(0,1),(1,2),(1,3),(2,4),(3,4),(5,0),(4,6)]) ~=? (intraE "x=0;if(true){x=0;}else{x=0;}x=0;")
  ]

ctxWhile = 
  [ "x=0;while(true){}" ~: (set [(0,1),(1,1),(2,0),(1,3)]) ~=? (intraE "x=0;while(true){}")
  , "x=0;while(true){}x=0;" ~: (set [(0,1),(1,1),(1,2),(3,0),(2,4)]) ~=? (intraE "x=0;while(true){}x=0;")
  , "x=0;while(true){z=0;z=1;}" ~: (set [(0,1),(1,2),(2,3),(3,1),(4,0),(1,5)]) ~=? (intraE "z=0;while(true){z=0;z=1;}")
  , "while(true){z=0;z=1;}x=0;" ~: (set [(0,1),(1,2),(2,0),(0,3),(4,0),(3,5)]) ~=? (intraE "while(true){z=0;z=1;}x=0;")
  , "x=0;while(true){z=0;z=1;}x=0;" ~: (set [(0,1),(1,2),(1,4),(2,3),(3,1),(5,0),(4,6)]) ~=? (intraE "x=0;while(true){z=0;z=1;}x=0;")
  ]

compWhile = 
  [ "while(true){while(true){}}" ~: (set [(0,1),(1,0),(1,1),(2,0),(0,3)]) ~=? (intraE "while(true){while(true){}}")
  ]

continue = 
  [ "while(true){x=0;continue;x=1;}x=2;" ~: (set [(0,1),(0,4),(1,2),(2,0),(5,0)]) ~=? (intraE "while(true){x=0;continue;x=1;}x=2;"),
    "while(true){x=0;x=1;continue;}x=2;" ~: (set [(0,1),(0,4),(1,2),(2,3),(3,0),(5,0)]) ~=? (intraE "while(true){x=0;x=1;continue;}x=2;")
  ]

labContinue =
  [ "lab:while(true){x=0;continue lab;x=1;}x=2;" ~: 
      (set [(0,1),(0,4),(1,2),(2,0),(5,0)]) ~=? (intraE "lab:while(true){x=0;continue lab;x=1;}x=2;"),
    "lab:while(true){x=0;while(true){x=1;continue lab; x=2;}x=3;}x=4;" ~: 
      (set [(0,1),(0,7),(1,2),(2,3),(2,6),(3,4),(4,0),(6,0),(8,0)]) ~=? (intraE "lab:while(true){x=0;while(true){x=1;continue lab; x=2;}x=3;}x=4;"),
    "lab:while(true){x=0;lab:while(true){x=1;continue lab; x=2;}x=3;}x=4;" ~: 
      (set [(0,1),(0,7),(1,2),(2,3),(2,6),(3,4),(4,2),(6,0),(8,0)]) ~=? (intraE "lab:while(true){x=0;lab:while(true){x=1;continue lab; x=2;}x=3;}x=4;")
    --"lab:function f(x){x=x+1;lab:function y(z){return z;}continue lab;return x;}" ~: (set [(0,1),(1,2),(2,3),(3,4),(4,2)]) ~=? (intraE "lab:function f(x){x=x+1;lab:function y(){return 3;}continue lab;return 2*x;}")
  ]

labBreak =
  [ "lab:while(true){x=0;break lab;x=1;}x=2;" ~: 
      (set [(0,1),(0,4),(1,2),(2,0),(5,0)]) ~=? (intraE "lab:while(true){x=0;break lab;x=1;}x=2;"),
    "lab:while(true){x=0;while(true){x=1;break lab; x=2;}x=3;}x=4;" ~: 
      (set [(0,1),(0,7),(1,2),(2,3),(2,6),(3,4),(4,0),(6,0),(8,0)]) ~=? (intraE "lab:while(true){x=0;while(true){x=1;break lab; x=2;}x=3;}x=4;"),
    "lab:while(true){x=0;lab:while(true){x=1;break lab; x=2;}x=3;}x=4;" ~: 
      (set [(0,1),(0,7),(1,2),(2,3),(2,6),(3,4),(4,2),(6,0),(8,0)]) ~=? (intraE "lab:while(true){x=0;lab:while(true){x=1;break lab; x=2;}x=3;}x=4;")
  ]
  
primFunc = 
  [ "function f(){}f();" ~: [(2,0,1,3)] ~=? (inter "function f(){}f();")
  , "function f(){}f();" ~: (set [(0,1),(4,2),(3,5)]) ~=? (intraE "function f(){}f();")

  , "function f(){x=0;}f();" ~: [(3,0,2,4)] ~=? (inter "function f(){x=0;}f();")
  , "function f(){x=0;}f();" ~: (set [(0,1),(1,2),(5,3),(4,6)]) ~=? (intraE "function f(){x=0;}f();")

  , "function f(){f();}f();" ~: [(1,0,3,2),(4,0,3,5)] ~=? (inter "function f(){f();}f();")
  , "function f(){f();}f();" ~: (set [(0,1),(2,3),(6,4),(5,7)]) ~=? (intraE "function f(){f();}f();")

  , "function f(){}f();f();" ~: [(2,0,1,3),(4,0,1,5)] ~=? (inter "function f(){}f();f();")
  , "function f(){}f();f();" ~: 
      (set [(0,1),(3,4),(6,2),(5,7)]) ~=? (intraE "function f(){}f();f();")

  , "function f(){}f();x=0;f();" ~: [(2,0,1,3),(5,0,1,6)] ~=? (inter "function f(){}f();x=0;f();")
  , "function f(){}f();x=0;f();" ~: 
      (set [(0,1),(3,4),(4,5),(7,2),(6,8)]) ~=? (intraE "function f(){}f();x=0;f();")

  , "function f(x){x=0;}x=3;f(x);x=2;" ~:
      (set [(0,1),(1,2),(3,4),(5,6),(7,3),(6,8)]) ~=? (intraE "function f(x){x=0;}x=3;f(x);x=2;")
  ]

compFunc = 
  [ "function f(){if(true){x=0;}else{x=0;}}f();" ~: 
      (set [(0,1),(1,2),(1,3),(2,4),(3,4),(7,5),(6,8)]) ~=? (intraE "function f(){if(true){x=0;}else{x=0;}}f();")

  , "function f(){while(true){}}f();" ~: 
      (set [(0,1),(1,1),(1,2),(5,3),(4,6)]) ~=? (intraE "function f(){while(true){}}f();")

  , "function f(){while(true){x=0;}}f();" ~: 
      (set [(0,1),(1,2),(1,3),(2,1),(6,4),(5,7)]) ~=? (intraE "function f(){while(true){x=0;}}f();")

  -- put composite tests with breaks, and labelled statements here
  ]

paramFunc =
  [ "function f(x){}f(3);" ~:
      (set [(0,1),(4,2),(3,5)]) ~=? (intraE "function f(x){}f(3);")

  , "function f(x){x=0;}x=3;f(x);x=2;" ~:
      (set [(0,1),(1,2),(3,4),(5,6),(7,3),(6,8)]) ~=? (intraE "function f(x){x=0;}x=3;f(x);x=2;")
  ]

primReturn =
  [ "function f(){return;}f();" ~: [(3,0,2,4)] ~=? (inter "function f(){return;}f();")

  , "function f(){return;}f();" ~: (set [(0,1),(1,2),(5,3),(4,6)]) ~=? (intraE "function f(){return;}f();")

  , "function f(){return 7641 - 1467;}f();" ~: (set [(0,1),(1,2),(5,3),(4,6)]) ~=? (intraE "function f(){return 7641 - 1467;}f();")
  ]

