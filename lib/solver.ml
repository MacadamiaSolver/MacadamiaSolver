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
    | Ast.Pow (_, _) ->
        0
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
      | Ast.Mul (lhs, rhs) ->
          let v, a = teval rhs in
          let var = internal s in
          ( var
          , a |> Nfa.intersect (NfaCollection.mul ~res:var ~lhs ~rhs:v (deg ()))
          )
          (* let rec teval_mul a b = *)
          (*   match a with *)
          (*     | 0 -> *)
          (*         let var = internal s in *)
          (*         (var, NfaCollection.eq_const var 0 (deg ())) *)
          (*     | 1 -> *)
          (*         teval b *)
          (*     | _ -> ( *)
          (*       match a mod 2 with *)
          (*         | 0 -> *)
          (*             let tv, ta = teval_mul (a / 2) b in *)
          (*             let res = internal s in *)
          (*             ( res *)
          (*             , NfaCollection.add ~lhs:tv ~rhs:tv ~sum:res (deg ()) *)
          (*               |> Nfa.intersect ta ) *)
          (*         | 1 -> *)
          (*             let tv, ta = teval_mul (a - 1) b in *)
          (*             let uv, ua = teval b in *)
          (*             let res = internal s in *)
          (*             ( res *)
          (*             , NfaCollection.add ~lhs:tv ~rhs:uv ~sum:res (deg ()) *)
          (*               |> Nfa.intersect ta |> Nfa.intersect ua ) *)
          (*         | _ -> *)
          (*             assert false ) *)
          (* in *)
          (* let v, nfa = teval_mul a b in *)
          (* (v, nfa) *)
      | Ast.Pow (_, x) -> (
        match x with
          | Ast.Var x ->
              let var = var_exn ("2**" ^ x) in
              (var, NfaCollection.isPowerOf2 var)
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
            NfaCollection.n 32 |> return
        | Ast.False ->
            NfaCollection.z 32 |> return
        | Ast.Eq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.eq lv rv (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Leq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
            NfaCollection.leq lv rv (deg ())
            |> Nfa.intersect la |> Nfa.intersect ra
            |> Nfa.truncate (deg ())
            |> return
        | Ast.Geq (l, r) ->
            let lv, la = teval s l in
            let rv, ra = teval s r in
            reset_internals ();
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
  (res, vars) |> return

let ( let* ) = Result.bind

let log2 n =
  let rec helper acc = function 0 -> acc | n -> helper (acc + 1) (n / 2) in
  helper (-1) n

let%expect_test "Proof for all x exists x + 1" =
  Format.printf "%d" (log2 4);
  [%expect {| 2 |}]

let%expect_test "Proof for all x exists x + 1" =
  Format.printf "%d" (log2 6);
  [%expect {| 2 |}]

let%expect_test "Proof for all x exists x + 1" =
  Format.printf "%d" (log2 1);
  [%expect {| 0 |}]

let _pow2 n =
  match n with
    | 0 ->
        1
    | n ->
        List.init (n - 1) (Fun.const 2) |> List.fold_left ( * ) 1

let gen_list_n n =
  let rec helper acc = function 0 -> [0] | n -> helper (n :: acc) (n - 1) in
  helper [] n |> List.rev

(*let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []*)

let is_exp var = String.starts_with ~prefix:"2**" var

let get_exp var =
  assert (is_exp var);
  String.sub var 3 (String.length var - 3)

let decide_order vars =
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
  let perms = perms (Map.keys vars) in
  List.filter
    (fun perm ->
      Base.List.for_alli
        ~f:(fun i var ->
          if is_exp var then
            let x = get_exp var in
            List.find_index (fun y -> x = y) perm
            |> Option.value ~default:9999999
            > i
          else true )
        perm )
    perms

let nfa_for_exponent2 s var var2 chrob =
  let deg () = Map.length s.vars in
  chrob
  |> List.map (fun (a, c) ->
         let old_internal_counter = !internal_counter in
         let a_var = internal s in
         let var2_plus_a = internal s in
         let t = internal s in
         let c_mul_t = internal s in
         let internal = internal s in
         let nfa =
           Nfa.project
             [var2_plus_a; c_mul_t; internal; t]
             (Nfa.intersect
                (NfaCollection.add ~lhs:var2_plus_a ~rhs:c_mul_t ~sum:var
                   (deg ()) )
                (Nfa.intersect
                   (Nfa.intersect
                      (NfaCollection.add ~sum:var2_plus_a ~lhs:var2 ~rhs:a_var
                         (deg ()) )
                      (NfaCollection.eq_const a_var a (deg ())) )
                   (NfaCollection.mul ~res:c_mul_t ~lhs:c ~rhs:t (deg ())) ) )
         in
         internal_counter := old_internal_counter;
         nfa )

let _ = nfa_for_exponent2

let nfa_for_exponent s var newvar chrob =
  let deg () = Map.length s.vars in
  chrob
  |> List.concat_map (fun (a, c) ->
         if c = 0 then
           List.init (a + 10) (( + ) a)
           |> List.map (fun x ->
                  let log = log2 x in
                  (x - log, log, 0) )
           |> List.filter (fun (t, _, _) -> t = a)
         else c |> gen_list_n |> List.map (fun d -> (a, d, c)) )
  |> List.map (fun (a, d, c) ->
         let old_internal_counter = !internal_counter in
         (* s.vars *)
         (* |> Map.iteri ~f:(fun ~key ~data -> *)
         (*        Format.printf "%s -> %d\n\n" key data ); *)
         let a_plus_d = internal s in
         let t = internal s in
         let c_mul_t = internal s in
         let internal = internal s in
         (* Format.printf *)
         (*   "a_plus_d -> %d\nt -> %d\nc_mul_t -> %d\ninternal -> %d\n" a_plus_d t *)
         (*   c_mul_t internal; *)
         let nfa =
           Nfa.project [a_plus_d; c_mul_t; t]
             (Nfa.intersect
                (NfaCollection.add ~lhs:a_plus_d ~rhs:c_mul_t ~sum:var (deg ()))
                (Nfa.intersect
                   (NfaCollection.eq_const a_plus_d (a + d) (deg ()))
                   (NfaCollection.mul ~res:c_mul_t ~lhs:c ~rhs:t (deg ())) ) )
         in
         (* Format.printf "nfa_for_exponent (a=%d,d=%d,c=%d): old_var nfa: %a\n" a *)
         (*   d c Nfa.format_nfa nfa; *)
         let n =
           List.init (a + 2) (( + ) a)
           |> List.filter (fun x -> x - log2 x >= a)
           |> List.hd
         in
         (* Format.printf "nfa_for_exponent (a=%d,d=%d,c=%d): n: %d\n" a d c n; *)
         let newvar_nfa = NfaCollection.torename newvar d c in
         (* Format.printf "nfa_for_exponent (a=%d,d=%d,c=%d): newvar_var nfa: %a\n" *)
         (*   a d c Nfa.format_nfa newvar_nfa; *)
         let geq_nfa =
           NfaCollection.geq var internal (deg ())
           |> Nfa.intersect (NfaCollection.eq_const internal n (deg ()))
         in
         (* Format.printf "nfa_for_exponent (a=%d,d=%d,c=%d): geq nfa: %a\n" a d c *)
         (*   Nfa.format_nfa geq_nfa; *)
         let nfa =
           nfa |> Nfa.truncate 32
           |> Nfa.intersect newvar_nfa (* TODO: add minimization here *)
           |> Nfa.intersect geq_nfa |> Nfa.truncate 32 |> Nfa.project [internal]
         in
         internal_counter := old_internal_counter;
         (* s.vars *)
         (* |> Map.iteri ~f:(fun ~key ~data -> *)
         (*        Format.printf "%s -> %d\n" key data ); *)
         (* Format.printf "nfa_for_exponent (a=%d,d=%d,c=%d): final nfa: %a\n" a d *)
         (*   c Nfa.format_nfa nfa; *)
         nfa )

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
  let nfa = Nfa.minimize nfa in
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

(*let () =
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
  ()*)

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

let%expect_test "Decide order basic" =
  let s = ref {preds= []; vars= Map.empty; total= 0; progress= 0} in
  Format.printf "%a"
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
       (Format.pp_print_list
          ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
          Format.pp_print_string ) )
    ( {|(2 ** x = y) & y = 3|} |> Parser.parse_formula |> Result.get_ok
    |> eval !s |> Result.get_ok |> snd |> decide_order );
  [%expect {| 2**x x y; 2**x y x; y 2**x x |}]

let proof_semenov formula =
  internal_counter := 0;
  let* nfa, vars = eval !s formula in
  let nfa = Nfa.minimize nfa in
  let s = {!s with vars} in
  let get_deg x = Map.find_exn vars x in
  let orders : string list list = decide_order vars in
  let first x =
    x
    |> Seq.find (function Ok true | Error _ -> true | Ok false -> false)
    |> function Some x -> x | None -> Ok false
  in
  let rec proof_order nfa order =
    (* Format.printf "Order: [%a]\n%!" *)
    (*   (Format.pp_print_list *)
    (*      ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ") *)
    (*      Format.pp_print_string ) *)
    (*   order; *)
    let nfa = Nfa.minimize nfa in
    (* Format.printf "nfa: %a\n" Nfa.format_nfa nfa; *)
    match order with
      | [] ->
          nfa |> Nfa.run_nfa
      | x :: y :: tl when (not (is_exp y)) && is_exp x ->
          proof_order (Nfa.project [get_deg y] nfa) (x :: tl)
      | x :: tl -> (
        match is_exp x with
          | false ->
              proof_order (Nfa.project [get_deg x] nfa) tl
          | true -> (
            match List.length tl with
              | 0 ->
                  nfa |> Nfa.project [get_deg x] |> Nfa.run_nfa
              | _ ->
                  let deg () = Map.length s.vars in
                  let old_counter = !internal_counter in
                  let inter = internal s in
                  let next = List.nth tl 0 in
                  let temp =
                    if is_exp next then get_deg (get_exp next) else inter
                  in
                  let x' = get_exp x in
                  let zero_nfa =
                    Nfa.intersect
                      (NfaCollection.eq_const (Map.find_exn s.vars x) 1 (deg ()))
                      (NfaCollection.eq_const (Map.find_exn s.vars x') 0
                         (deg ()) )
                    |> Nfa.truncate (deg ())
                  in
                  (* Format.printf "zero_nfa:\n%a\n" Nfa.format_nfa zero_nfa; *)
                  let t =
                    nfa |> Nfa.intersect zero_nfa
                    |> Nfa.project [Map.find_exn s.vars x]
                  in
                  if proof_order t tl then true
                  else
                    let nfa =
                      if is_exp next then nfa
                      else
                        nfa |> Nfa.truncate 32
                        |> Nfa.intersect
                             (NfaCollection.torename2 (get_deg x') inter)
                    in
                    (* vars *)
                    (* |> Map.iteri ~f:(fun ~key ~data -> *)
                    (*        Format.printf "%s -> %d\n" key data ); *)
                    (* Format.printf "internal -> %d" inter; *)
                    (* Format.printf "nfa with limitations: %a\n" Nfa.format_nfa *)
                    (*   nfa; *)
                    let t =
                      Nfa.get_chrobaks_sub_nfas nfa ~res:(get_deg x) ~temp
                    in
                    (* t *)
                    (* |> List.iteri (fun i (nfa, list) -> *)
                    (*        Format.printf "chrobak subnfa %d:\n" i; *)
                    (*        list *)
                    (*        |> Format.printf "chrobak: [%a]\n" *)
                    (*             (Format.pp_print_list *)
                    (*                ~pp_sep:(fun ppf () -> *)
                    (*                  Format.fprintf ppf ", " ) *)
                    (*                (fun ppf (a, b) -> *)
                    (*                  Format.fprintf ppf "%d+%dk" a b ) ); *)
                    (*        Format.printf "%a\n\n" Nfa.format_nfa nfa ); *)
                    let result =
                      t |> List.to_seq
                      |> Seq.flat_map (fun (nfa, chrobak) ->
                             let a =
                               (* Format.printf "Next is exp: %b\n" (is_exp next); *)
                               ( match is_exp next with
                                 | false ->
                                     nfa_for_exponent s (Map.find_exn s.vars x')
                                       inter chrobak
                                 | true ->
                                     let y = get_exp next in
                                     nfa_for_exponent2 s
                                       (Map.find_exn s.vars x')
                                       (Map.find_exn s.vars y) chrobak )
                               |> List.map (Nfa.intersect nfa)
                             in
                             (* a *)
                             (* |> List.iter *)
                             (*      (Format.printf "intersected: %a\n" *)
                             (*         Nfa.format_nfa ); *)
                             a |> List.to_seq )
                      |> Seq.map (Nfa.project [get_deg x; inter])
                      |> Seq.map (fun nfa -> proof_order nfa tl)
                      |> Seq.exists Fun.id
                    in
                    internal_counter := old_counter;
                    result ) )
  in
  orders |> List.to_seq
  |> Seq.map (fun order ->
         let len = List.length order in
         (* Format.printf "%a\n" Nfa.format_nfa nfa; *)
         let* nfa =
           if len <= 1 then Ok nfa
           else
             let* order_nfa, _ =
               eval s
                 ( Seq.zip
                     (order |> List.to_seq |> Seq.take (len - 1))
                     (order |> List.to_seq |> Seq.drop 1)
                 |> Seq.map (fun (x, y) -> Ast.Geq (Ast.Var x, Ast.Var y))
                 |> List.of_seq
                 |> function
                 | [] -> failwith "" | h :: tl -> List.fold_left Ast.mand h tl
                 )
             in
             (* Format.printf "%a\n" Nfa.format_nfa order_nfa; *)
             Nfa.intersect nfa order_nfa |> Nfa.minimize |> Result.ok
         in
         (* Format.printf "nfa_with_order: %a\n" Nfa.format_nfa nfa; *)
         proof_order nfa order |> Result.ok )
  |> first
