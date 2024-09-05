open Lib

module TestHelloWorld = struct
  let test () =
    Alcotest.(check string)
      "same string" "Hello world" (HelloWorld.getString ())
end
