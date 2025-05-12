Test Frobenius coin problem for 7 and 11

  $ Chro ./examples/fcp_7_11.smt2
  sat

Test Frobenius coin problem for 2 and 4

  $ Chro ./examples/fcp_2_4.smt2
  unsat

Test ExEy y >=0 x & 2**y = x & x > 4

  $ Chro ./examples/basic-exp-sat.smt2
  sat
  x = 8  y = 3  

Test Ex x > 2**x

  $ Chro ./examples/basic-exp-unsat.smt2
  unsat

Test basic bitvectors

  $ Chro ./examples/basic-bitvector-bitwise.smt2
  sat
  s = 0b11 (3) t = 0b10011 (19) 

Test double exponent

  $ Chro ./examples/double_exp.smt2
  unsat

Test Frobenius coin problem with exponential restrictions

  $ Chro ./examples/fcp_7_11_with_exps.smt2
  sat
