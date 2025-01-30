module Set = Base.Set.Poly
module Map = Base.Map.Poly

type t =
  { preds:
      (string * string list * Ast.formula * Nfa.t * (string, int) Map.t) list
  ; vars: (string, int) Map.t
  ; total: int
  ; progress: int }

let ( let* ) = Result.bind

let return = Result.ok

let throw_if cond a = if cond then Result.error a else Result.ok ()

let default_s () = {preds= []; vars= Map.empty; total= 0; progress= 0}

let s = ref (default_s ())

let collect f =
  Ast.fold
    (fun acc ast ->
      match ast with
        | Ast.Exists (xs, _) | Ast.Any (xs, _) ->
            Set.union acc (Set.of_list xs)
        | Ast.Pred (_, _) ->
            acc
        | _ ->
            acc )
    (fun acc x ->
      match x with
        | Ast.Var x ->
            Set.add acc x
        | Ast.Pow (_, x) -> (
          match x with
            | Ast.Var x ->
                Set.add acc ("2**" ^ x)
            | _ ->
                failwith "unimplemented" )
        | _ ->
            acc )
    Set.empty f

let _estimate f = Ast.fold (fun acc _ -> acc + 1) (fun acc _ -> acc + 1) 0 f

let internal_counter = ref 0

let internal s =
  internal_counter := !internal_counter + 1;
  !internal_counter - 1 + Map.length s.vars

let teval s ast =
  let var_exn v = Map.find_exn s.vars v in
  let rec teval ast =
    match ast with
      | Ast.Var a ->
          let var = var_exn a in
          (var, NfaCollection.n ())
      | Ast.Const a ->
          let var = internal s in
          (var, NfaCollection.eq_const var a)
      | Ast.Add (l, r) ->
          let lv, la = teval l in
          let rv, ra = teval r in
          let res = internal s in
          ( res
          , NfaCollection.add ~lhs:lv ~rhs:rv ~sum:res
            |> Nfa.intersect la |> Nfa.intersect ra )
      | Ast.Mul (a, b) ->
          let rec teval_mul a b =
            match a with
              | 0 ->
                  let var = internal s in
                  (var, NfaCollection.eq_const var 0)
              | 1 ->
                  teval b
              | _ -> (
                match a mod 2 with
                  | 0 ->
                      let tv, ta = teval_mul (a / 2) b in
                      let res = internal s in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:tv ~sum:res
                        |> Nfa.intersect ta )
                  | 1 ->
                      let tv, ta = teval_mul (a - 1) b in
                      let uv, ua = teval b in
                      let res = internal s in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:uv ~sum:res
                        |> Nfa.intersect ta |> Nfa.intersect ua )
                  | _ ->
                      assert false )
          in
          let v, nfa = teval_mul a b in
          (v, nfa)
      | Ast.Pow (_, x) -> (
        match x with
          | Ast.Var x ->
              (var_exn ("2**" ^ x), NfaCollection.n ())
          | _ ->
              failwith "unimplemented" )
  in
  let nfa = teval ast in
  nfa

let eval s ast =
  let vars =
    collect ast |> Set.to_list
    |> List.mapi (fun i x -> (x, i))
    |> Map.of_alist_exn
  in
  let s = {preds= s.preds; vars; total= 0; progress= 0} in
  let deg () = Map.length s.vars in
  let var_exn v = Map.find_exn s.vars v in
  let reset_internals () = internal_counter := Map.length s.vars in
  let rec eval ast =
    let nfa =
      match ast with
        | Ast.True ->
            NfaCollection.n () |> return
        | Ast.False ->
            NfaCollection.z () |> return
        | Ast.Eq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.eq lv rv |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Leq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.leq lv rv |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Geq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.geq lv rv |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Lt (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.lt lv rv |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Gt (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.gt lv rv |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Mnot f ->
            let* nfa = eval f in
            nfa |> Nfa.invert |> return
        | Ast.Mand (f1, f2) ->
            let* la = eval f1 in
            let* ra = eval f2 in
            Nfa.intersect la ra |> return
        | Ast.Mor (f1, f2) ->
            let* la = eval f1 in
            let* ra = eval f2 in
            Nfa.unite la ra |> return
        | Ast.Mimpl (f1, f2) ->
            let* la = eval f1 in
            let* ra = eval f2 in
            Nfa.unite (la |> Nfa.invert) ra |> return
        | Ast.Exists (x, f) ->
            let* nfa = eval f in
            let x = List.map var_exn x in
            nfa |> Nfa.project x |> return
        | Ast.Any (x, f) ->
            let* nfa = eval f in
            let x = List.map var_exn x in
            nfa |> Nfa.invert |> Nfa.project x |> Nfa.invert |> return
        | Ast.Pred (name, args) ->
            let* _, pred_params, _, pred_nfa, pred_vars =
              List.find_opt
                (fun (pred_name, _, _, _, _) -> pred_name = name)
                s.preds
              |> Option.to_result
                   ~none:(Format.sprintf "Unknown predicate: %s" name)
            in
            let args = List.map (teval s) args in
            reset_internals ();
            let map =
              List.mapi
                (fun i (v, _) ->
                  (v, List.nth pred_params i |> Map.find_exn pred_vars) )
                args
              |> Map.of_alist_exn
            in
            let nfa = pred_nfa |> Nfa.reenumerate map in
            List.fold_left Nfa.intersect nfa (List.map snd args) |> return
        | _ ->
            failwith "unimplemented"
    in
    nfa
  in
  let* res = eval ast in
  (res, vars) |> return

let ( let* ) = Result.bind

let dump f =
  let* nfa, _ = eval !s f in
  Format.asprintf "%a" Nfa.format_nfa (nfa |> Nfa.minimize) |> return

let list () =
  let rec aux = function
    | [] ->
        ()
    | (name, params, f, _, _) :: xs ->
        Format.printf "%s %a = %a\n%!" name
          (Format.pp_print_list Format.pp_print_string)
          params Ast.pp_formula f;
        aux xs
  in
  aux !s.preds

let pred name params f =
  let* nfa, vars = eval !s f in
  s :=
    { preds= (name, params, f, nfa, vars) :: !s.preds
    ; total= !s.total
    ; vars= !s.vars
    ; progress= !s.progress };
  return ()

let proof f =
  let* _ =
    throw_if
      (Ast.for_some
         (fun _ -> false)
         (function Ast.Pow (_, _) -> true | _ -> false)
         f )
      ""
  in
  let* nfa, _ = f |> eval !s in
  Nfa.run nfa |> return

let proof_semenov f =
  let* nfa, _ = f |> eval !s in
  Nfa.run nfa |> return

let%expect_test
    "Proof any x > 7 can be represented as a linear combination of 3 and 5" =
  Format.printf "%b"
    ( {|AxEyEz x = 3y + 5z | x <= 7|} |> Parser.parse_formula |> Result.get_ok
    |> proof |> Result.get_ok );
  [%expect {| true |}]

let%expect_test
    "Disproof any x > 6 can be represented as a linear combination of 3 and 5" =
  Format.printf "%b"
    ( {|AxEyEz x = 3y + 5z | x <= 6|} |> Parser.parse_formula |> Result.get_ok
    |> proof |> Result.get_ok );
  [%expect {| false |}]

let%expect_test "Proof for all x exists x + 1" =
  Format.printf "%b"
    ( {|AxEy y = x + 1|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Disproof for all x exists x - 1" =
  Format.printf "%b"
    ( {|AxEy x = y + 1|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| false |}]

let%expect_test "Proof simple existential formula" =
  Format.printf "%b"
    ( {|ExEy 15 = x + y & y <= 10|} |> Parser.parse_formula |> Result.get_ok
    |> proof |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Proof simple any quantified formula" =
  Format.printf "%b"
    ( {|Ax x = 2 | ~(x = 2)|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Proof 2 <= 3" =
  Format.printf "%b"
    ( {|2 <= 3|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Proof zero is the least" =
  Format.printf "%b"
    ( {|Ax x >= 0|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Disproof 3 >= 15" =
  Format.printf "%b"
    ( {|3 >= 15|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| false |}]

let%expect_test "Proof less than 1 is zero" =
  Format.printf "%b"
    ( {|Ax x < 1 -> x = 0|} |> Parser.parse_formula |> Result.get_ok |> proof
    |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Proof if x > 3 and y > 4 then x + y > 7" =
  Format.printf "%b"
    ( {|AxAy x > 3 & y > 4 -> x + y > 7|} |> Parser.parse_formula
    |> Result.get_ok |> proof |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Proof sum of two even is even" =
  s := default_s ();
  {|Ey x = 2y|} |> Parser.parse_formula |> Result.get_ok |> pred "even" ["x"]
  |> Result.get_ok;
  Format.printf "%b"
    ( {|AxAyAz x + y = z & even(x) & even(y) -> even(z)|}
    |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok );
  s := default_s ();
  [%expect {| true |}]

let%expect_test "Proof sum of two even plus one is odd" =
  s := default_s ();
  {|Ey x = 2y|} |> Parser.parse_formula |> Result.get_ok |> pred "even" ["x"]
  |> Result.get_ok;
  Format.printf "%b"
    ( {|AxAyAz x + y = z & even(x) & even(y) -> ~even(z + 1)|}
    |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok );
  s := default_s ();
  [%expect {| true |}]

let%expect_test "Disproof sum of two even plus one is even" =
  s := default_s ();
  {|Ey x = 2y|} |> Parser.parse_formula |> Result.get_ok |> pred "even" ["x"]
  |> Result.get_ok;
  Format.printf "%b"
    ( {|AxAyAz x + y = z & even(x) & even(y) -> even(z + 1)|}
    |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok );
  s := default_s ();
  [%expect {| false |}]

let%expect_test "Proof a number is even iff it's not odd" =
  s := default_s ();
  {|Ey x = 2y|} |> Parser.parse_formula |> Result.get_ok |> pred "even" ["x"]
  |> Result.get_ok;
  {|Ey x = 2y + 1|} |> Parser.parse_formula |> Result.get_ok |> pred "odd" ["x"]
  |> Result.get_ok;
  Format.printf "%b"
    ( {|Ax (even(x) -> ~odd(x)) & (~odd(x) -> even(x))|} |> Parser.parse_formula
    |> Result.get_ok |> proof |> Result.get_ok );
  s := default_s ();
  [%expect {| true |}]
