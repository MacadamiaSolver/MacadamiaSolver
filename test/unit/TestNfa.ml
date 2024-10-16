open Lib
open Bits
module Map = Nfa.Map

let ( let* ) = Option.bind

let l = Map.of_alist_exn

let test_simple_nfa () =
  let run nfa str =
    str |> List.map (fun x -> Map.singleton () x) |> Nfa.run_nfa nfa
  in
  let nfa =
    Nfa.create_nfa
      ~transitions:
        [ (0, l [((), O)], 1)
        ; (1, l [((), I)], 0)
        ; (1, l [((), I)], 1)
        ; (0, l [((), O)], 2) ]
      ~start:[0] ~final:[2]
  in
  Alcotest.(check bool) "same bool" true (run nfa [O; I; I; O]);
  Alcotest.(check bool) "same bool" false (run nfa [O; I; I; I])

let test_map_varname () =
  let run nfa str var =
    str |> List.map (fun x -> Map.singleton var x) |> Nfa.run_nfa nfa
  in
  let nfa =
    Nfa.create_nfa
      ~transitions:
        [ (0, l [("x", O)], 1)
        ; (1, l [("x", I)], 0)
        ; (1, l [("x", I)], 1)
        ; (0, l [("x", O)], 2) ]
      ~start:[0] ~final:[2]
  in
  Alcotest.(check bool) "same bool" true (run nfa [O; I; I; O] "x");
  Alcotest.(check bool) "same bool" false (run nfa [O; I; I; I] "x");
  Alcotest.(check bool) "same bool" false (run nfa [O; I; I; O] "y");
  let nfa = Nfa.map_varname (fun _ -> "y") nfa in
  Alcotest.(check bool) "same bool" true (run nfa [O; I; I; O] "y");
  Alcotest.(check bool) "same bool" false (run nfa [O; I; I; I] "y");
  Alcotest.(check bool) "same bool" false (run nfa [O; I; I; O] "x")

let test_intersect_nfa () =
  let run nfa strX strY =
    List.map2 (fun x y -> l [("x", x); ("y", y)]) strX strY |> Nfa.run_nfa nfa
  in
  let nfa1 =
    Nfa.create_nfa
      ~transitions:[(0, l [("x", I)], 1); (1, l [("x", O)], 1)]
      ~start:[0] ~final:[1]
  in
  let nfa2 =
    Nfa.create_nfa
      ~transitions:[(0, l [("y", I)], 1); (1, l [("y", O)], 1)]
      ~start:[0] ~final:[1]
  in
  let one = [I; O; O] in
  let zero = [O; O; O] in
  let inter = Nfa.intersect nfa1 nfa2 in
  (* x = 1 test *)
  Alcotest.(check bool) "same bool" true (run nfa1 one one);
  Alcotest.(check bool) "same bool" true (run nfa1 one zero);
  Alcotest.(check bool) "same bool" false (run nfa1 zero zero);
  Alcotest.(check bool) "same bool" false (run nfa1 zero one);
  (* y = 1 test *)
  Alcotest.(check bool) "same bool" true (run nfa2 one one);
  Alcotest.(check bool) "same bool" false (run nfa2 one zero);
  Alcotest.(check bool) "same bool" false (run nfa2 zero zero);
  Alcotest.(check bool) "same bool" true (run nfa2 zero one);
  (* x = 1 and y = 1 test *)
  Alcotest.(check bool) "same bool" true (run inter one one);
  Alcotest.(check bool) "same bool" false (run inter one zero);
  Alcotest.(check bool) "same bool" false (run inter zero zero);
  Alcotest.(check bool) "same bool" false (run inter zero one)

let test_project_nfa () =
  let run nfa strX strY =
    List.map2 (fun x y -> l [("x", x); ("y", y)]) strX strY |> Nfa.run_nfa nfa
  in
  let nfa =
    Nfa.create_nfa
      ~transitions:
        [(0, l [("x", I); ("y", I)], 1); (1, l [("x", O); ("y", O)], 1)]
      ~start:[0] ~final:[1]
  in
  let one = [I; O; O] in
  let zero = [O; O; O] in
  let proj = Nfa.project (( = ) "x") nfa in
  (* x = 1 and y = 1 test *)
  Alcotest.(check bool) "same bool" true (run nfa one one);
  Alcotest.(check bool) "same bool" false (run nfa one zero);
  Alcotest.(check bool) "same bool" false (run nfa zero zero);
  Alcotest.(check bool) "same bool" false (run nfa zero one);
  (* x = 1 test *)
  Alcotest.(check bool) "same bool" true (run proj one one);
  Alcotest.(check bool) "same bool" true (run proj one zero);
  Alcotest.(check bool) "same bool" false (run proj zero zero);
  Alcotest.(check bool) "same bool" false (run proj zero one)

let test_simple_dfa () =
  let run dfa str =
    str |> List.map (fun x -> Map.singleton () x) |> Nfa.run_dfa dfa
  in
  let dfa =
    Nfa.create_dfa ~transitions:[(0, l [((), I)], 1)] ~start:0 ~final:[1]
  in
  Alcotest.(check bool) "same bool" true (Result.is_ok dfa);
  let dfa = Result.get_ok dfa in
  Alcotest.(check bool) "same bool" true (run dfa [I]);
  Alcotest.(check bool) "same bool" false (run dfa [O])

let test_collisions_dfa () =
  let dfa =
    Nfa.create_dfa
      ~transitions:
        [ (0, l [((), O)], 1)
        ; (1, l [((), I)], 0)
        ; (1, l [((), I)], 1)
        ; (0, l [((), O)], 2) ]
      ~start:0 ~final:[1]
  in
  Alcotest.(check bool) "same bool" true (Result.is_error dfa)

let test_dfa_to_nfa () =
  let run nfa str =
    str |> List.map (fun x -> Map.singleton () x) |> Nfa.run_nfa nfa
  in
  let dfa =
    Nfa.create_dfa ~transitions:[(0, l [((), I)], 1)] ~start:0 ~final:[1]
  in
  Alcotest.(check bool) "same bool" true (Result.is_ok dfa);
  let nfa = Result.get_ok dfa |> Nfa.to_nfa in
  Alcotest.(check bool) "same bool" true (run nfa [I]);
  Alcotest.(check bool) "same bool" false (run nfa [O])

let tests =
  ( "Nfa"
  , [ Alcotest.test_case "" `Quick test_simple_nfa
    ; Alcotest.test_case "" `Quick test_map_varname
    ; Alcotest.test_case "" `Quick test_intersect_nfa
    ; Alcotest.test_case "" `Quick test_project_nfa
    ; Alcotest.test_case "" `Quick test_simple_dfa
    ; Alcotest.test_case "" `Quick test_collisions_dfa
    ; Alcotest.test_case "" `Quick test_dfa_to_nfa ] )
