Basic LIA tests

  $ Smtlib ./lia.smt2
  sat
  unsat
  sat
  sat
  sat
  sat
  sat
  unsat
  sat

Test Frobenious coin problem for 7 and 11

  $ Smtlib ./examples/LIA/fcp_7_11.smt2
  sat
  P = 59; 

Test Frobenious coin problem for 7, 11, and 13

  $ Smtlib ./examples/LIA/fcp_7_11_13.smt2
  sat
  P = 30; 

Test Frobenious coin problem for 2 and 4

  $ Smtlib ./examples/LIA/fcp_2_4.smt2
  unsat
  no model

Test for all nats exists bigger

  $ Smtlib ./examples/LIA/for-all-nats-exists-bigger.smt2
  sat
