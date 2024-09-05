open TestHelloWorld

let () =
  let open Alcotest in
  run "HelloWorld"
    [("getString", [test_case "Simple" `Quick TestHelloWorld.test])]
