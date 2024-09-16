let () =
  Alcotest.run "MacadamiaSolver"
    [TestParser.tests; TestNfa.tests; TestNfaCollection.tests]
