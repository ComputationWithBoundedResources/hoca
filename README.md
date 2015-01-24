Higher-Order Complexity Analysis
================================

Automatic complexity analysis tool for higher-order systems.
Currently it can translate a pure fragment of OCaml to first-order 
term rewrite systems (TRSs for short). 

Install
-------
For building, you need [ghc](http://www.haskell.org/ghc/) and 
[cabal](http://www.haskell.org/cabal/). 
To install, type `cabal install` in the root source folder.

Usage
-----
A program is specified as lambda-term enrichted by `let`, 
`let rec` and `match` expressions. 
See the [examples directory](https://github.com/mzini/hoca/tree/master/examples)
for the syntax of programs.
To translate a program to a TRS, type `pcf2trs <file>`
where `<file>` specifies the input program. For full options, type `pcf2trs --help`.
