Test ExEy y >=0 x & 2**y = x & x > 4

$ Smtlib ./examples/basic-exp-sat.smt2
sat
Unable to get model: Semenov arithmetic doesn't support getting a model yet

Test Ex x > 2**x

$ Smtlib ./examples/basic-exp-unsat.smt2
unsat

Test bad

$ Smtlib ./examples/bad-exp.smt2
error during script evaluation: '=' expected all arguments to be formulas or terms; if you meant term the problem is 'only base two is supported'; if you meant formulas the problem is 'unimplemented SMT-lib construction: (Smtlib.SpecConstant (Smtlib.Numeric 9))'

Test basic bitvectors

$ Smtlib ./examples/basic-bitvector-bitwise.smt2
sat
s = 0b11 (3) t = 0b10011 (19) 
