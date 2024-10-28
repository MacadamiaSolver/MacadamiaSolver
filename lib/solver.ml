module Set = Base.Set.Poly
module Map = Base.Map.Poly

type t =
  { preds: (string * string list * Ast.formula * Nfa.t) list
  ; vars: (string, int) Map.t
  ; total: int
  ; progress: int }

let ( let* ) = Result.bind

let return = Result.ok

let s = ref {preds= []; vars= Map.empty; total= 0; progress= 0}

let collect f =
  let rec collect_term = function
    | Ast.Const _ ->
        Set.empty
    | Ast.Var x ->
        Set.singleton x
    | Ast.Add (t1, t2) ->
        Set.union (collect_term t1) (collect_term t2)
    | Ast.Mul (_, t1) ->
        collect_term t1
  in
  let rec collect_formula = function
    | Ast.Eq (t1, t2)
    | Ast.Lt (t1, t2)
    | Ast.Gt (t1, t2)
    | Ast.Leq (t1, t2)
    | Ast.Geq (t1, t2)
    | Ast.Neq (t1, t2) ->
        Set.union (collect_term t1) (collect_term t2)
    | Ast.Mor (f1, f2) | Ast.Mand (f1, f2) | Ast.Mimpl (f1, f2) ->
        Set.union (collect_formula f1) (collect_formula f2)
    | Ast.Mnot f1 ->
        collect_formula f1
    | Ast.Exists (x, f1) | Ast.Any (x, f1) ->
        Set.add (collect_formula f1) x
    | Ast.Pred (_, args) ->
        List.fold_left
          (fun acc x -> Set.union acc (collect_term x))
          Set.empty args
    | _ ->
        Set.empty
  in
  collect_formula f |> Set.to_list
  |> List.mapi (fun i x -> (x, i))
  |> Map.of_alist_exn

(*let estimate f =
    let rec estimate_term = function
      | Ast.Const _ | Ast.Var _ ->
          1
      | Ast.Add (t1, t2) ->
          1 + estimate_term t1 + estimate_term t2
      | Ast.Mul (_, t1) ->
          1 + estimate_term t1
    in
    let rec estimate_formula = function
      | Ast.Eq (t1, t2)
      | Ast.Lt (t1, t2)
      | Ast.Gt (t1, t2)
      | Ast.Leq (t1, t2)
      | Ast.Geq (t1, t2)
      | Ast.Neq (t1, t2) ->
          1 + estimate_term t1 + estimate_term t2
      | Ast.Mor (f1, f2) | Ast.Mand (f1, f2) | Ast.Mimpl (f1, f2) ->
          1 + estimate_formula f1 + estimate_formula f2
      | Ast.Mnot f1 ->
          1 + estimate_formula f1
      | Ast.Exists (_, f1) | Ast.Any (_, f1) ->
          1 + estimate_formula f1
      | Ast.Pred (_, args) ->
          1 + List.fold_left (fun acc x -> acc + estimate_term x) 0 args
      | _ ->
          1
    in
    estimate_formula f

  let progress s =
    let pl = 12 in
    let rec repeat n s = if n <= 0 then "" else s ^ repeat (n - 1) s in
    let c =
      Float.of_int s.progress /. Float.of_int s.total *. Float.of_int pl
      |> Int.of_float
    in
    Printf.printf "%s" (repeat 80 "\b");
    Printf.printf "[%s%s] [%0#3d/%0#3d]%!" (repeat c "\u{2588}")
      (repeat (pl - c) " ")
      s.progress s.total*)

let internal_counter = ref 0

let teval s ast =
  let var_exn v = Map.find_exn s.vars v in
  let rec internals = function
    | Ast.Const _ ->
        1
    | Ast.Var _ ->
        0
    | Ast.Add (t1, t2) ->
        1 + internals t1 + internals t2
    | Ast.Mul (a, t1) ->
        let rec aux a b =
          match a with
            | 0 ->
                1
            | 1 ->
                internals b
            | _ -> (
              match a mod 2 with
                | 0 ->
                    aux (a / 2) b
                | 1 ->
                    aux (a - 1) b
                | _ ->
                    assert false )
        in
        aux a t1
  in
  let internal () =
    internal_counter := !internal_counter + 1;
    !internal_counter - 1 + Map.length s.vars
  in
  (*let internal_counter = ref (Map.length s.vars) in
    let internal () =
      internal_counter := !internal_counter + 1;
      !internal_counter - 1
    in*)
  let deg () = Map.length s.vars + internals ast in
  let rec teval ast =
    match ast with
      | Ast.Var a ->
          let var = var_exn a in
          (var, NfaCollection.n (deg ()))
      | Ast.Const a ->
          let var = internal () in
          (var, NfaCollection.eq_const var a (deg ()))
      | Ast.Add (l, r) ->
          let lv, la = teval l in
          let rv, ra = teval r in
          let res = internal () in
          ( res
          , NfaCollection.add ~lhs:lv ~rhs:rv ~sum:res (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra )
      | Ast.Mul (a, b) ->
          let rec teval_mul a b =
            match a with
              | 0 ->
                  let var = internal () in
                  (var, NfaCollection.eq_const var 0 (deg ()))
              | 1 ->
                  teval b
              | _ -> (
                match a mod 2 with
                  | 0 ->
                      let tv, ta = teval_mul (a / 2) b in
                      let res = internal () in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:tv ~sum:res (deg ())
                        |> Nfa.intersect ta )
                  | 1 ->
                      let tv, ta = teval_mul (a - 1) b in
                      let uv, ua = teval b in
                      let res = internal () in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:uv ~sum:res (deg ())
                        |> Nfa.intersect ta |> Nfa.intersect ua )
                  | _ ->
                      assert false )
          in
          let v, nfa = teval_mul a b in
          (v, nfa)
  in
  let nfa = teval ast in
  internal_counter := Map.length s.vars;
  nfa

let eval s ast =
  let vars = collect ast in
  List.iter (fun (x, y) -> Format.printf "%s=%i\n" x y) (vars |> Map.to_alist);
  let s = {preds= s.preds; vars; total= 0; progress= 0} in
  let deg () = Map.length s.vars in
  let var_exn v = Map.find_exn s.vars v in
  let rec eval ast =
    let nfa =
      match ast with
        | Ast.Eq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            NfaCollection.eq lv rv (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Leq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            NfaCollection.leq lv rv (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Geq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            NfaCollection.geq lv rv (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra
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
            let x = var_exn x in
            nfa |> Nfa.project [x] |> return
        | Ast.Any (x, f) ->
            let* nfa = eval f in
            let var = var_exn x in
            nfa |> Nfa.invert |> Nfa.project [var] |> Nfa.invert |> return
        (*| Ast.Pred (name, args) -> (
            let args = List.map (teval s) args in
            match
              List.find_opt
                (fun (pred_name, _, _, _) -> pred_name = name)
                s.preds
            with
              | Some (_, pred_params, _, pred_nfa) ->
                  let nfa =
                    pred_nfa
                    |> Nfa.map_varname (function
                         | Var s -> (
                           match List.find_index (( = ) s) pred_params with
                             | Some i -> (
                               match List.nth_opt args i with
                                 | Some (av, _) ->
                                     av
                                 | None ->
                                     Var s )
                             | None ->
                                 Var s )
                         | x ->
                             x )
                    |> List.fold_right
                         (fun acc a -> Nfa.intersect acc a)
                         (List.map (fun (_, arg) -> arg) args)
                    |> Nfa.project (function
                         | Var _ ->
                             true
                         | Internal _ ->
                             false )
                  in
                  Result.ok nfa
              | None ->
                  Printf.sprintf "Unknown predicate %s" name |> Result.error )*)
        | _ ->
            failwith "unimplemented"
    in
    nfa
  in
  let res = eval ast in
  Format.printf "\n%!"; res

let dump f =
  let* nfa = eval !s f in
  Format.asprintf "%a" Nfa.format_nfa nfa |> return

let list () =
  let rec aux = function
    | [] ->
        ()
    | (name, params, f, _) :: xs ->
        Format.printf "%s %a = %a\n%!" name
          (Format.pp_print_list Format.pp_print_string)
          params Ast.pp_formula f;
        aux xs
  in
  aux !s.preds

let pred name params f =
  let* nfa = eval !s f in
  s :=
    { preds= (name, params, f, nfa) :: !s.preds
    ; total= !s.total
    ; vars= !s.vars
    ; progress= !s.progress };
  return ()

let proof f =
  let* nfa = eval !s f in
  Nfa.run_nfa nfa |> return
