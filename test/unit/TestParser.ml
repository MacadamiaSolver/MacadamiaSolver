open Lib

let test_exists_bigger () =
  Alcotest.(check string)
    "same string" "(Any x (Exists y (Equals (Var x) (Add (Var y) (Const 1)))))"
    (Ast.string_of_formula (Parser.parse "AxEy x = y + 1"))

let test_no_biggest_int () =
  Alcotest.(check string)
    "same string"
    "(Not (Exists x (Any y (Exists z (Equals (Var x) (Add (Var y) (Var z)))))))"
    (Ast.string_of_formula (Parser.parse "~ExAyEz(x = y + z)"))

let test_divisible_by_7 () =
  Alcotest.(check string)
    "same string"
    "(Exists x (Equals (Var y) (Add (Add (Add (Add (Add (Add (Var x) (Var x)) \
     (Var x)) (Var x)) (Var x)) (Var x)) (Var x))))"
    (Ast.string_of_formula (Parser.parse "Ex y = x + x + x + x + x + x + x"))

let test_sum_of_evens_is_even () =
  Alcotest.(check string)
    "same string"
    "(Any x (Any y (Impl (And (Exists z (Equals (Var x) (Add (Var z) (Var \
     z)))) (Exists w (Equals (Var y) (Add (Var w) (Var w))))) (Exists v \
     (Equals (Add (Var x) (Var y)) (Add (Var v) (Var v)))))))"
    (Ast.string_of_formula
       (Parser.parse
          "AxAy((Ez x = z + z) & (Ew y = w + w) -> (Ev x + y = v + v))" ) )

let tests =
  ( "Parser"
  , [ Alcotest.test_case "Exists bigger int for any int" `Quick
        test_exists_bigger
    ; Alcotest.test_case "No biggest int exists" `Quick test_no_biggest_int
    ; Alcotest.test_case "Divisible by 7 integers" `Quick test_divisible_by_7
    ; Alcotest.test_case "Sum of evens is even" `Quick test_sum_of_evens_is_even
    ] )
