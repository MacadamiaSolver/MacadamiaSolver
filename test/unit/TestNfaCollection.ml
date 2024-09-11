open Lib
open Bits
module Map = Nfa.Map

let ( let* ) = Option.bind

let l = Map.of_alist_exn

type add = Lhs | Rhs | Sum

let test_add_nfa () =
  let run dfa lhs rhs sum =
    let rec helper lhs rhs sum =
      match (lhs, rhs, sum) with
        | [], [], [] ->
            []
        | h1 :: tl1, h2 :: tl2, h3 :: tl3 ->
            Map.of_alist_exn [(Lhs, h1); (Rhs, h2); (Sum, h3)]
            :: helper tl1 tl2 tl3
        | _ ->
            failwith "Expected same size lists"
    in
    helper lhs rhs sum |> Nfa.run_dfa dfa
  in
  let dfa = NfaCollection.Add.add ~lhs:Lhs ~rhs:Rhs ~sum:Sum in
  (* 5+4=9 *)
  Alcotest.(check bool)
    "same bool" true
    (run dfa [I; O; I; O] [O; O; I; O] [I; O; O; I]);
  (* 3+2!=8 *)
  Alcotest.(check bool)
    "same bool" false
    (run dfa [I; I; O; O] [O; I; O; O] [O; O; O; I])

let test_add_same_number_nfa () =
  let run dfa x y =
    let rec helper x y =
      match (x, y) with
        | [], [] ->
            []
        | h1 :: tl1, h2 :: tl2 ->
            Map.of_alist_exn [("x", h1); ("y", h2)] :: helper tl1 tl2
        | _ ->
            failwith "Expected same size lists"
    in
    helper x y |> Nfa.run_dfa dfa
  in
  let dfa = NfaCollection.Add.add ~lhs:"x" ~rhs:"x" ~sum:"y" in
  (* 2+2=4 *)
  Alcotest.(check bool) "same bool" true (run dfa [O; I; O; O] [O; O; I; O]);
  (* 3+3!=7 *)
  Alcotest.(check bool) "same bool" false (run dfa [I; I; O; O] [I; I; I; O])

let test_eq_nfa () =
  let run dfa x y =
    let rec helper x y =
      match (x, y) with
        | [], [] ->
            []
        | h1 :: tl1, h2 :: tl2 ->
            Map.of_alist_exn [("x", h1); ("y", h2)] :: helper tl1 tl2
        | _ ->
            failwith "Expected same size lists"
    in
    helper x y |> Nfa.run_dfa dfa
  in
  let dfa = NfaCollection.Eq.eq "x" "y" in
  (* 3=3 *)
  Alcotest.(check bool) "same bool" true (run dfa [I; I; O; O] [I; I; O; O]);
  (* 3!=4 *)
  Alcotest.(check bool) "same bool" false (run dfa [I; I; O; O] [O; O; I; O])

let test_eq_const_nfa () =
  let run dfa x = x |> List.map (Map.singleton "x") |> Nfa.run_dfa dfa in
  let dfa = NfaCollection.Eq.eq_const "x" 7 in
  (* 7=7 *)
  Alcotest.(check bool) "same bool" true (run dfa [I; I; I; O]);
  (* 6!=7 *)
  Alcotest.(check bool) "same bool" false (run dfa [O; I; I; O])

let tests =
  ( "Nfa collection"
  , [ Alcotest.test_case "" `Quick test_add_nfa
    ; Alcotest.test_case "" `Quick test_add_same_number_nfa
    ; Alcotest.test_case "" `Quick test_eq_nfa
    ; Alcotest.test_case "" `Quick test_eq_const_nfa ] )
(*     ; Alcotest.test_case "" `Quick test_intersect_nfa *)
(*     ; Alcotest.test_case "" `Quick t1 *)
(*     ; Alcotest.test_case "" `Quick t2 ] ) *)
