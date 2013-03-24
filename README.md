# Constant propagation for a small subset of JavaScript

Contents
-------------------------------------------------------------
1. Environment
2. Building
3. Running
4. Documentation

-------------------------------------------------------------

1. Environment
-------------------------------------------------------------

See js.cabal

2. Building
-------------------------------------------------------------

Build and install the project:
> make

Clean the project
> make clean

3. Running
-------------------------------------------------------------
Example programs are located in the examples directory. 

Running an example:
> cat examples/programs/prog1 | ./dist/build/js-cp/js-cp cp

The flow graph can be visualized by graphviz:
> cat examples/programs/prog1 | ./dist/build/js-cp/js-cp cfg-merged > out.dot ; dot -Tpng out.dot > out.png

For more information on the available options:
> ./dist/build/js-cp/js-cp

The project also comes with a set of unit tests for the flow graph, analysis, and constant folding.
To run the tests:
> ./dist/build/unittests/unittests

Or alternatively experiment interactively:
> cd src
> ghci Components.hs
> defaultPipeline' "function id(x){return x;}id(1);id(2);"
