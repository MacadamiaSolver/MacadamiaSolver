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

let s = ref {preds= []; vars= Map.empty; total= 0; progress= 0}

let collect f =
  Ast.fold
    (fun acc ast ->
      match ast with
        | Ast.Exists (xs, _) | Ast.Any (xs, _) ->
            Set.union acc (Set.of_list xs)
        | _ ->
            acc )
    (fun acc x -> match x with Ast.Var x -> Set.add acc x | _ -> acc)
    Set.empty f

let _estimate f = Ast.fold (fun acc _ -> acc + 1) (fun acc _ -> acc + 1) 0 f

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

let internal s =
  internal_counter := !internal_counter + 1;
  !internal_counter - 1 + Map.length s.vars

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
    | _ ->
        failwith "Unimplemented"
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
          let var = internal s in
          (var, NfaCollection.eq_const var a (deg ()))
      | Ast.Add (l, r) ->
          let lv, la = teval l in
          let rv, ra = teval r in
          let res = internal s in
          ( res
          , NfaCollection.add ~lhs:lv ~rhs:rv ~sum:res (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra )
      | Ast.Mul (a, b) ->
          let rec teval_mul a b =
            match a with
              | 0 ->
                  let var = internal s in
                  (var, NfaCollection.eq_const var 0 (deg ()))
              | 1 ->
                  teval b
              | _ -> (
                match a mod 2 with
                  | 0 ->
                      let tv, ta = teval_mul (a / 2) b in
                      let res = internal s in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:tv ~sum:res (deg ())
                        |> Nfa.intersect ta )
                  | 1 ->
                      let tv, ta = teval_mul (a - 1) b in
                      let uv, ua = teval b in
                      let res = internal s in
                      ( res
                      , NfaCollection.add ~lhs:tv ~rhs:uv ~sum:res (deg ())
                        |> Nfa.intersect ta |> Nfa.intersect ua )
                  | _ ->
                      assert false )
          in
          let v, nfa = teval_mul a b in
          (v, nfa)
      | _ ->
          failwith "Unimplemented"
  in
  let nfa = teval ast in
  internal_counter := Map.length s.vars;
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
  let rec eval ast =
    let nfa =
      match ast with
        | Ast.True ->
            NfaCollection.n 32 |> return
        | Ast.False ->
            NfaCollection.z 32 |> return
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
            let x = List.map var_exn x in
            nfa |> Nfa.project x |> return
        | Ast.Any (x, f) ->
            let* nfa = eval f in
            let x = List.map var_exn x in
            nfa |> Nfa.invert |> Nfa.project x |> Nfa.invert |> return
        | Ast.Pred (name, args) ->
            let* _, _pred_params, _, pred_nfa, _pred_vars =
              List.find_opt
                (fun (pred_name, _, _, _, _) -> pred_name = name)
                s.preds
              |> Option.to_result
                   ~none:(Format.sprintf "Unknown predicate: %s" name)
            in
            let _args = List.map (teval s) args in
            let nfa = pred_nfa in
            nfa |> return
        | Ast.Pow2 x ->
            let v, a = teval s x in
            NfaCollection.isPowerOf2 v |> Nfa.intersect a
            |> Nfa.truncate (deg ())
            |> return
        | _ ->
            failwith "unimplemented"
    in
    nfa
  in
  let* res = eval ast in
  Format.printf "\n%!";
  (res, vars) |> return

let ( let* ) = Result.bind

let log2 n =
  let rec helper acc = function 0 -> acc | n -> helper (acc + 1) (n / 2) in
  helper 0 n

let _pow2 n =
  match n with
    | 0 ->
        1
    | n ->
        List.init (n - 1) (Fun.const 2) |> List.fold_left ( * ) 1

let gen_list_n n =
  let rec helper acc = function 0 -> [0] | n -> helper (n :: acc) (n - 1) in
  helper [] n |> List.rev

let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []

type orderEntry = Var of string | Power of string

let decide_order f =
  (* The call accepts only conjuctions *)
  assert (
    Ast.for_all
      (function Ast.Mor _ -> false | Ast.Mimpl _ -> false | _ -> true)
      (fun _ -> true)
      f );
  let vars_and_pows =
    Ast.fold
      (fun acc _ -> acc)
      (fun acc t ->
        match t with
          | Ast.Var _ ->
              Set.add acc t
          | Ast.Const _ ->
              acc
          | Ast.Pow (c, x) ->
              assert (c = 2);
              assert (match x with Var _ -> true | _ -> false);
              Set.add acc t
          | _ ->
              acc )
      Set.empty f
  in
  let rec perms list =
    let a =
      if List.length list <> 0 then
        List.mapi
          (fun i el ->
            let list = List.filteri (fun j _ -> i <> j) list in
            List.map (fun list' -> el :: list') (perms list) )
          list
        |> List.concat
      else [[]]
    in
    a
  in
  let perms = perms (vars_and_pows |> Set.to_list) in
  let perms =
    List.filter
      (fun perm ->
        Base.List.for_alli
          ~f:(fun i ast ->
            match ast with
              | Ast.Pow (_, x) -> (
                match x with
                  | Ast.Var x ->
                      List.find_index (fun y -> Ast.var x = y) perm
                      |> Option.value ~default:9999999
                      > i
                  | _ ->
                      assert false )
              | _ ->
                  true )
          perm )
      perms
  in
  List.fold_left
    (fun acc perm ->
      let order_ast =
        List.fold_left
          (fun acc i ->
            let t1 = List.nth perm i in
            let t2 = List.nth perm (i + 1) in
            Ast.geq t1 t2 |> Ast.mand acc )
          (Ast.mtrue ())
          (0 -- (List.length perm - 2))
      in
      let ast = f in
      Ast.mor (Ast.mand order_ast ast) acc )
    (Ast.mfalse ()) perms

let nfa_for_exponent s var newvar chrob =
  let deg () = Map.length s.vars in
  chrob
  |> List.concat_map (fun (a, c) ->
         if c = 0 then
           List.init a (( + ) (a + 1))
           |> List.map (fun x -> (x, log2 x, 0))
           |> List.filter (fun (x, log, _) -> x - log = a)
         else c |> gen_list_n |> List.map (fun d -> (a, d, c)) )
  |> List.map (fun (a, d, c) ->
         let ast =
           Ast.Exists
             ( [var ^ "$"]
             , Eq
                 ( Var var
                 , Add (Add (Const a, Const d), Mul (c, Var (var ^ "$"))) ) )
         in
         let s =
           { s with
             vars=
               Map.add_exn ~key:(var ^ "$")
                 ~data:(succ (s.vars |> Map.data |> List.fold_left max ~-1))
                 s.vars }
         in
         let* nfa, _ = eval s ast in
         let n =
           List.init a (( + ) (a + 1))
           |> List.filter (fun x -> x - log2 x >= a)
           |> List.hd
         in
         Format.printf "\n%d\n%!" n;
         let internal = internal s in
         nfa |> Nfa.truncate 32
         |> Nfa.intersect (NfaCollection.torename newvar d c)
            (* TODO: add minimization here *)
         |> Nfa.intersect
              ( NfaCollection.geq (Map.find_exn s.vars var) internal (deg ())
              |> Nfa.intersect (NfaCollection.eq_const internal n (deg ())) )
         |> Nfa.truncate (deg ())
         |> Result.ok )
  |> Base.Result.all

(* TODO: REMOVE THIS BEFORE MERGE *)

(* let () = *)
(*   let s = *)
(*     { preds= [] *)
(*     ; vars= Map.of_alist_exn [("x", 0); ("u", 1)] *)
(*     ; total= 0 *)
(*     ; progress= 0 } *)
(*   in *)
(*   let nfa = *)
(*     nfa_for_exponent s "x" 1 [(3, 5)] |> Result.get_ok |> Nfa.truncate 32 *)
(*   in *)
(*   let s = Format.asprintf "%a" Nfa.format_nfa nfa in *)
(*   let line = "tmp" in *)
(*   (* let dot_file = Format.sprintf "dumps/\"%s.dot\"" line in *) *)
(*   (* let svg_file = Format.sprintf "dumps/\"%s.svg\"" line in *) *)
(*   let oc = open_out (Format.sprintf "dumps/%s.dot" line) in *)
(*   (* let command = *) *)
(*   (*   Format.sprintf "mkdir -p dumps/; dot -Tsvg %s > %s; xdg-open %s" dot_file *) *)
(*   (*     svg_file svg_file *) *)
(*   (* in *) *)
(*   Printf.fprintf oc "%s" s; *)
(*   close_out oc; *)
(*   (* Sys.command command |> ignore; *) *)
(*   let amount = 100 in *)
(*   Seq.init amount (fun x -> *)
(*       Nfa.intersect *)
(*         (NfaCollection.eq_const 0 x 32) *)
(*         (NfaCollection.eq_const 1 (x |> log2 |> pow2) 32) ) *)
(*   |> Seq.map (Nfa.intersect nfa) *)
(*   |> Seq.map (Nfa.truncate 0) *)
(*   |> Seq.map Nfa.run_nfa *)
(*   |> Seq.zip (Seq.init amount Fun.id) *)
(*   (* |> Seq.filter snd |> Seq.take 1 *) *)
(*   |> Seq.for_all (fun (n, res) -> *)
(*          Format.printf "%d (%d): %b\n" n (n |> log2 |> pow2) res; *)
(*          true ) *)
(*   |> ignore *)

(* TODO: END OF THING TO REMOVE *)

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

let () =
  let ast =
    "z = w & w = x + y & z >= w & w >= x & x >= y & ~(x >= z) & ~(y >= w)"
    |> Parser.parse_formula |> Result.get_ok
  in
  let vars =
    collect ast |> Set.to_list
    |> List.mapi (fun i x -> (x, i))
    |> Map.of_alist_exn
  in
  List.iter (fun (x, y) -> Format.printf "%s=%i\n" x y) (vars |> Map.to_alist);
  let s = {preds= !s.preds; vars; total= 0; progress= 0} in
  let nfa, _vars = ast |> eval s |> Result.get_ok in
  let res = Map.find_exn s.vars "z" in
  let temp = Map.find_exn s.vars "w" in
  let sub_nfa = Nfa.get_exponent_sub_nfa nfa ~res ~temp in
  Format.printf "07.11.24: %a\n%!" Nfa.format_nfa sub_nfa;
  ()

let proof f =
  let* nfa, _ = f |> Optimizer.optimize |> eval !s in
  Nfa.run_nfa nfa |> return

let%expect_test "Proof any x > 7 can be represented as a linear combination of \
                 3 and 5" =
  Format.printf "%b"
    ( {|AxEyEz x = 3y + 5z | x <= 7|} |> Parser.parse_formula |> Result.get_ok
    |> proof |> Result.get_ok );
  [%expect {| true |}]

let%expect_test "Disproof any x > 6 can be represented as a linear combination \
                 of 3 and 5" =
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

let%expect_test "Decide order basic" =
  Format.printf "%a" Ast.pp_formula
    ( {|(2 ** x = y) & y = 3|} |> Parser.parse_formula |> Result.get_ok
    |> decide_order );
  [%expect
    {| ((((True & ((2 ** x) >= y)) & (y >= x)) & (((2 ** x) = y) & (y = 3))) | ((((True & ((2 ** x) >= x)) & (x >= y)) & (((2 ** x) = y) & (y = 3))) | ((((True & (y >= (2 ** x))) & ((2 ** x) >= x)) & (((2 ** x) = y) & (y = 3))) | False))) |}]

let () = Var "" |> ignore

let () = Power "" |> ignore

let proof_semenov formula =
  let* nfa, vars = eval !s formula in
  let s = {!s with vars} in
  let orders : orderEntry list list = failwith "" (* decide_order formula *) in
  let any = List.exists (function Ok true -> true | _ -> false) in
  let rec proof_order nfa = function
    | [] ->
        nfa |> Nfa.is_graph |> Result.ok
    | Var x :: tl ->
        proof_order (Nfa.project [Map.find_exn vars x] nfa) tl
    | Power x :: (Var _ :: _ as tl) ->
        let inter = internal s in
        let chrobak = Nfa.chrobak nfa in
        let* exp_nfa = nfa_for_exponent s x inter chrobak in
        exp_nfa
        |> List.map (Nfa.intersect nfa)
        |> List.map (fun nfa -> proof_order nfa tl)
        |> any |> Result.ok
    | Power _x :: (Power _y :: _ as _tl) ->
        failwith ""
    | [Power x] ->
        nfa |> Nfa.project [Map.find_exn vars x] |> Nfa.is_graph |> Result.ok
  in
  orders |> List.map (proof_order nfa) |> any |> Result.ok

let () =
  let nfa, _vars =
    "Et x = 5t" |> Parser.parse_formula |> Result.get_ok |> eval !s
    |> Result.get_ok
  in
  Format.printf "%a\n" Nfa.format_nfa nfa;
  let chrobak = Nfa.chrobak nfa in
  Format.printf "07.11.24: [%a]\n%!"
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
       (fun ppf (a, b) -> Format.fprintf ppf "(%d,%d)" a b) )
    chrobak;
  ()
