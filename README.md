Higher-Order Complexity Analysis
================================

Automatic complexity analysis tool for higher-order systems.
Currently it can translate a pure fragment of Ocaml to first-order 
term rewrite systems (TRSs for short). 

Install
-------
To install, you need [ghc](http://www.haskell.org/ghc/) and 
[cabal](http://www.haskell.org/cabal/). To install, type  
$ cabal install
in the root source folder.

Usage
-----
See the examples directory for the syntax of programs.
To translate a program to a TRS, type  
`$ pcf2trs <file>`
where `file` specifies the program. For full options, type `pcf2trs`.






