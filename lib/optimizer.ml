let contains var f =
  Ast.for_some
    (function Ast.Exists (a, _) | Ast.Any (a, _) -> a = var | _ -> false)
    (function Ast.Var a -> List.mem a var | _ -> false)
    f

let move_quantifiers_closer formula =
  let rec aux f =
    let f' =
      Ast.map
        (function
          | (Ast.Exists (x, f') | Ast.Any (x, f')) as f -> (
              let quantifier_ast = Ast.quantifier_ast_exn f in
              match f' with
                | Ast.Mor (f1, f2)
                | Ast.Mand (f1, f2)
                | Ast.Miff (f1, f2)
                | Ast.Mimpl (f1, f2) -> (
                    let binconj_ast = Ast.binconj_ast_exn f' in
                    let l1 = contains x f1 in
                    let l2 = contains x f2 in
                    match (l1, l2) with
                      | true, true ->
                          f
                      | false, false ->
                          f'
                      | true, false ->
                          binconj_ast (quantifier_ast x f1) f2
                      | false, true ->
                          binconj_ast f1 (quantifier_ast x f2) )
                | _ ->
                    if contains x f' then f else f' )
          | _ as f ->
              f )
        Fun.id f
    in
    if f' = f then f' else aux f'
  in
  aux formula

let quantifier_union f =
  Ast.map
    (function
      | Ast.Exists (x, f') as f -> (
        match f' with
          | Ast.Exists (y, f'') ->
              Ast.exists (List.append x y) f''
          | _ ->
              f )
      | Ast.Any (x, f') as f -> (
        match f' with
          | Ast.Any (y, f'') ->
              Ast.any (List.append x y) f''
          | _ ->
              f )
      | _ as f ->
          f )
    Fun.id f

let optimize f = f |> move_quantifiers_closer |> quantifier_union
