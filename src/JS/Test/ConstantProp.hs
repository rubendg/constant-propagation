module JS.Test.ConstantProp where
import Test.HUnit
import JS.Analysis.ConstantPropagation
import JS.Analysis.CP.Base
import Components

cpTests = TestList []

run = cpFlatten . defaultPipeline

{-
tests = 
  [ "x=0;" ~: ([(0,[],"x",Bottom),(1,[],"x",Bottom)],[(0,[],"x",Z 0),(1,[],"x",Bottom)]) ~=? run "x=0;" 
  , "while(true){}" ~: ([],[]) ~=? run "while(true){}"
 
  , "x=0;while(true){x=2;}x=1;"
      ~: ([(0,"x",Bottom),(1,"x",Top),(2,"x",Top),(3,"x",Top)]
         ,[(0,"x",Z 0),(1,"x",Top),(2,"x",Z 2),(3,"x",Z 1)]
         )
      ~=? run "x=0;while(true){x=2;}x=1;"

  , "y=2;z=1;while(x>0){z=z*y;}x=x-1;"
      ~: ([(0,"x",Bottom),(0,"y",Bottom),(0,"z",Bottom),(1,"x",Bottom),(1,"y",Z 2),
          (1,"z",Bottom),(2,"x",Bottom),(2,"y",Z 2),(2,"z",Top),(3,"x",Bottom),(3,"y",Z 2),
          (3,"z",Top),(4,"x",Bottom),(4,"y",Z 2),(4,"z",Top)]
         ,[(0,"x",Bottom),(0,"y",Z 2),(0,"z",Bottom),(1,"x",Bottom),
           (1,"y",Z 2),(1,"z",Z 1),(2,"x",Bottom),(2,"y",Z 2),(2,"z",Top),
           (3,"x",Bottom),(3,"y",Z 2),(3,"z",Top),(4,"x",Bottom),(4,"y",Z 2),(4,"z",Top)]
         )
      ~=? run "y=2;z=1;while(x>0){z=z*y;}x=x-1;"
  ]
-}
