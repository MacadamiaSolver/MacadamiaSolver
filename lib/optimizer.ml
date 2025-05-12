(*
   let contains var f =
  Ast.for_some
    (function
      | Ast.Exists (a, _) | Ast.Any (a, _) -> a = var
      | _ -> false)
    (function
      | Ast.Var a -> List.mem a var
      | _ -> false)
    f
;;

let move_quantifiers_closer formula =
  let rec aux f =
    let f' =
      Ast.map
        (function
          | (Ast.Exists (x, f') | Ast.Any (x, f')) as f ->
            let quantifier_ast = Ast.quantifier_ast_exn f in
            (match f' with
             | Ast.Mor (f1, f2)
             | Ast.Mand (f1, f2)
             | Ast.Miff (f1, f2)
             | Ast.Mimpl (f1, f2) ->
               let binconj_ast = Ast.binconj_ast_exn f' in
               let l1 = contains x f1 in
               let l2 = contains x f2 in
               (match l1, l2 with
                | true, true -> f
                | false, false -> f'
                | true, false -> binconj_ast (quantifier_ast x f1) f2
                | false, true -> binconj_ast f1 (quantifier_ast x f2))
             | _ -> if contains x f' then f else f')
          | _ as f -> f)
        Fun.id
        f
    in
    if f' = f then f' else aux f'
  in
  aux formula
;;

let get_rid_of_forall formula =
  Ast.map
    (function
      | Ast.Any (x, f') -> Ast.mnot (Ast.exists x (Ast.mnot f'))
      | _ as f -> f)
    Fun.id
    formula
;;

let apply_demourgan_law formula =
  let rec aux f =
    let f' =
      Ast.map
        (function
          | Ast.Mnot f' as f ->
            (match f' with
             | Ast.Mor (f1, f2) -> Ast.mand (Ast.mnot f1) (Ast.mnot f2)
             | Ast.Mand (f1, f2) -> Ast.mor (Ast.mnot f1) (Ast.mnot f2)
             | _ -> f)
          | _ as f -> f)
        Fun.id
        f
    in
    if f' = f then f' else aux f'
  in
  aux formula
;;

let simplify_negation formula =
  let rec aux f =
    let f' =
      Ast.map
        (function
          | Ast.Mnot f' as f ->
            (match f' with
             | Ast.Mnot f'' -> f''
             | Ast.Leq (f1, f2) -> Ast.gt f1 f2
             | Ast.Geq (f1, f2) -> Ast.lt f1 f2
             | Ast.Gt (f1, f2) -> Ast.leq f1 f2
             | Ast.Lt (f1, f2) -> Ast.geq f1 f2
             | Ast.Eq (f1, f2) -> Ast.neq f1 f2
             | Ast.Neq (f1, f2) -> Ast.eq f1 f2
             | _ -> f)
          | _ as f -> f)
        Fun.id
        f
    in
    if f' = f then f' else aux f'
  in
  aux formula
;;

let quantifier_union f =
  Ast.map
    (function
      | Ast.Exists (x, f') as f ->
        (match f' with
         | Ast.Exists (y, f'') -> Ast.exists (List.append x y) f''
         | _ -> f)
      | Ast.Any (x, f') as f ->
        (match f' with
         | Ast.Any (y, f'') -> Ast.any (List.append x y) f''
         | _ -> f)
      | _ as f -> f)
    Fun.id
    f
;;

let optimize f =
  f
  |> move_quantifiers_closer
  |> quantifier_union
  |> get_rid_of_forall
  |> apply_demourgan_law
  |> simplify_negation
;;

let%expect_test "Move existential quantifiers closer" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|ExEyEz x + y = 2 & z = 15|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> move_quantifiers_closer);
  [%expect {| ((Ex (Ey ((x + y) = 2))) & (Ez (z = 15))) |}]
;;

let%expect_test "Move for all quantifiers closer" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|AxAy y = 2 | y = 3 | y = 4 | x = 2|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> move_quantifiers_closer);
  [%expect {| ((Ay (((y = 2) | (y = 3)) | (y = 4))) | (Ax (x = 2))) |}]
;;

let%expect_test "Existential quantifier union" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|ExEyEz x + y + z = 15|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> quantifier_union);
  [%expect {| (Ex y z (((x + y) + z) = 15)) |}]
;;

let%expect_test "For all quantifier union" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|AxAyAz x + y + z = 15|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> quantifier_union);
  [%expect {| (Ax y z (((x + y) + z) = 15)) |}]
;;

let%expect_test "Replace for all with existential quantifiers" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|Ax x >= 0|} |> Parser.parse_formula |> Result.get_ok |> get_rid_of_forall);
  [%expect {| (~ (Ex (~ (x >= 0)))) |}]
;;

let%expect_test "Simplify negations" =
  Format.printf
    "%a"
    Ast.pp_formula
    ({|~(a = 1) & ~(b > 1) & ~(c < 1) & ~(d >= 1) & ~(e <= 1) & ~(f != 1) & ~(~(g = 1)) & ~(h = 1 -> i = 2)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> simplify_negation);
  [%expect
    {| ((((((((a != 1) & (b <= 1)) & (c >= 1)) & (d < 1)) & (e > 1)) & (f = 1)) & (g = 1)) & (~ ((h = 1) -> (i = 2)))) |}]
;;
*)
