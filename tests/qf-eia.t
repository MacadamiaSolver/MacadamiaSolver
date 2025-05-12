Test ExEy y >=0 x & 2**y = x & x > 4

  $ Smtlib ./examples/QF_EIA/basic-exp-sat.smt2
  sat
  Unable to get model: Semenov arithmetic doesn't support getting a model yet

Test Ex x > 2**x

  $ Smtlib ./examples/QF_EIA/basic-exp-unsat.smt2
  unsat
