(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

module Set = Base.Set.Poly
module Map = Base.Map.Poly

type t =
  { preds : (string * string list * Ast.formula * Nfa.t * (string, int) Map.t) list
  ; rpreds : (string * Regex.t * Nfa.t) list
  ; vars : (string, int) Map.t
  ; total : int
  ; progress : int
  }

let ( let* ) = Result.bind
let return = Result.ok
let fail = Result.error
let throw_if cond a = if cond then Result.error a else Result.ok ()
let default_s () = { preds = []; rpreds = []; vars = Map.empty; total = 0; progress = 0 }
let s = ref (default_s ())

let collect f =
  Ast.fold
    (fun acc ast ->
       match ast with
       | Ast.Exists (xs, _) | Ast.Any (xs, _) -> Set.union acc (Set.of_list xs)
       | Ast.Pred (_, _) -> acc
       | _ -> acc)
    (fun acc x ->
       match x with
       | Ast.Var x -> Set.add acc x
       | Ast.Pow (_, x) ->
         (match x with
          | Ast.Var x -> Set.add acc ("2**" ^ x)
          | _ -> failwith "unimplemented")
       | _ -> acc)
    Set.empty
    f
;;

let collect_free f =
  Ast.fold
    (fun acc ast ->
       match ast with
       | Ast.Exists (xs, _) | Ast.Any (xs, _) -> Set.diff acc (Set.of_list xs)
       | Ast.Pred (_, _) -> acc
       | _ -> acc)
    (fun acc x ->
       match x with
       | Ast.Var x -> Set.add acc x
       | Ast.Pow (_, x) ->
         (match x with
          | Ast.Var x -> Set.add acc x
          | _ -> failwith "unimplemented")
       | _ -> acc)
    Set.empty
    f
;;

let _estimate f = Ast.fold (fun acc _ -> acc + 1) (fun acc _ -> acc + 1) 0 f
let internal_counter = ref 0

let internal s =
  internal_counter := !internal_counter + 1;
  !internal_counter - 1 + Map.length s.vars
;;

let teval s ast =
  let var_exn v = Map.find_exn s.vars v in
  let rec teval ast =
    let teval2 build_nfa l r =
      let lv, la = teval l in
      let rv, ra = teval r in
      let res = internal s in
      res, build_nfa ~lhs:lv ~rhs:rv ~res |> Nfa.intersect la |> Nfa.intersect ra
    in
    match ast with
    | Ast.Var a ->
      let var = var_exn a in
      var, NfaCollection.n ()
    | Ast.Const a ->
      let var = internal s in
      var, NfaCollection.eq_const var a
    | Ast.Add (l, r) -> teval2 NfaCollection.add l r
    | Ast.Bvand (l, r) -> teval2 NfaCollection.bvand l r
    | Ast.Bvor (l, r) -> teval2 NfaCollection.bvor l r
    | Ast.Bvxor (l, r) -> teval2 NfaCollection.bvxor l r
    | Ast.Mul (a, b) ->
      let rec teval_mul a b =
        match a with
        | 0 ->
          let var = internal s in
          var, NfaCollection.eq_const var 0
        | 1 -> teval b
        | _ ->
          (match a mod 2 with
           | 0 ->
             let tv, ta = teval_mul (a / 2) b in
             let res = internal s in
             res, NfaCollection.add ~lhs:tv ~rhs:tv ~res |> Nfa.intersect ta
           | 1 ->
             let tv, ta = teval_mul (a - 1) b in
             let uv, ua = teval b in
             let res = internal s in
             ( res
             , NfaCollection.add ~lhs:tv ~rhs:uv ~res
               |> Nfa.intersect ta
               |> Nfa.intersect ua )
           | _ -> assert false)
      in
      let v, nfa = teval_mul a b in
      v, nfa
    | Ast.Pow (_, x) ->
      (match x with
       | Ast.Var x ->
         let var = var_exn ("2**" ^ x) in
         var, NfaCollection.n ()
       | _ -> failwith "unimplemented")
  in
  let nfa = teval ast in
  nfa
;;

let eval s ast =
  let vars =
    collect ast |> Set.to_list |> List.mapi (fun i x -> x, i) |> Map.of_alist_exn
  in
  let s = { preds = s.preds; rpreds = s.rpreds; vars; total = 0; progress = 0 } in
  let deg () = Map.length s.vars in
  let var_exn v = Map.find_exn s.vars v in
  let reset_internals () = internal_counter := Map.length s.vars in
  let rec eval ast =
    let nfa =
      match ast with
      | Ast.True -> NfaCollection.n () |> return
      | Ast.False -> NfaCollection.z () |> return
      | Ast.Eq (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.eq lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Neq (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.neq lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Leq (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.leq lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Geq (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.geq lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Lt (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.lt lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Gt (l, r) ->
        let lv, la = teval s l in
        let rv, ra = teval s r in
        reset_internals ();
        NfaCollection.gt lv rv
        |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.truncate (deg ())
        |> return
      | Ast.Mnot f ->
        let* nfa = eval f in
        nfa |> Nfa.invert |> Nfa.minimize |> return
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
        nfa |> Nfa.project x |> Nfa.minimize |> return
      | Ast.Any (x, f) ->
        let* nfa = eval f in
        let x = List.map var_exn x in
        nfa |> Nfa.invert |> Nfa.project x |> Nfa.invert |> Nfa.minimize |> return
      | Ast.Pred (name, args) ->
        (match
           List.find_opt (fun (pred_name, _, _, _, _) -> pred_name = name) s.preds
         with
         | Some pred ->
           let _, pred_params, _, pred_nfa, pred_vars = pred in
           let* () =
             let pl = List.length pred_params in
             let al = List.length args in
             Format.sprintf
               "expected %d arguments for predicate %s but found %d arguments"
               pl
               name
               al
             |> throw_if (pl <> al)
           in
           let args = List.map (teval s) args in
           let map =
             List.mapi
               (fun i (v, _) -> v, List.nth pred_params i |> Map.find_exn pred_vars)
               args
             |> Map.of_alist_exn
           in
           reset_internals ();
           let nfa = pred_nfa |> Nfa.reenumerate map in
           let nfa = List.fold_left Nfa.intersect nfa (List.map snd args) in
           nfa |> Nfa.truncate (deg ()) |> return
         | None ->
           (match
              List.find_opt (fun (rpred_name, _, _) -> name = rpred_name) s.rpreds
            with
            | Some rpred ->
              let _, _, rpred_nfa = rpred in
              let args = List.map (teval s) args in
              let map = List.mapi (fun i (v, _) -> v, i) args |> Map.of_alist_exn in
              reset_internals ();
              let nfa = rpred_nfa |> Nfa.reenumerate map in
              let nfa = List.fold_left Nfa.intersect nfa (List.map snd args) in
              nfa |> Nfa.truncate (deg ()) |> return
            | None -> Format.sprintf "unknown predicate %s" name |> fail))
      | _ -> failwith "unimplemented"
    in
    nfa
  in
  let* res = eval ast in
  (res, vars) |> return
;;

let ( let* ) = Result.bind

let dump f =
  let* nfa, _ = eval !s f in
  Format.asprintf "%a" Nfa.format_nfa (nfa |> Nfa.minimize) |> return
;;

let list () =
  let rec aux = function
    | [] -> ()
    | (name, params, f, _, _) :: xs ->
      Format.printf
        "%s %a = %a\n%!"
        name
        (Format.pp_print_list Format.pp_print_string)
        params
        Ast.pp_formula
        f;
      aux xs
  in
  Format.printf "Usual predicates:\n%!";
  aux !s.preds;
  let rec aux = function
    | [] -> ()
    | (name, re, _) :: xs ->
      Format.printf "%s = %a\n%!" name Regex.pp re;
      aux xs
  in
  Format.printf "\nRegular predicates:\n%!";
  aux !s.rpreds;
  Format.printf "\n\n%!"
;;

let pred name params f =
  let* nfa, vars = eval !s f in
  s
  := { preds = (name, params, f, nfa, vars) :: !s.preds
     ; rpreds = !s.rpreds
     ; total = !s.total
     ; vars = !s.vars
     ; progress = !s.progress
     };
  return ()
;;

let predr name re =
  let nfa = Regex.to_nfa re in
  s
  := { preds = !s.preds
     ; rpreds = (name, re, nfa) :: !s.rpreds
     ; total = !s.total
     ; vars = !s.vars
     ; progress = !s.progress
     };
  return ()
;;

let log2 n =
  let rec helper acc = function
    | 0 -> acc
    | n -> helper (acc + 1) (n / 2)
  in
  helper (-1) n
;;

let pow2 n = List.init n (Fun.const 2) |> List.fold_left ( * ) 1

let gen_list_n n =
  let rec helper acc = function
    | 0 -> [ 0 ]
    | n -> helper (n :: acc) (n - 1)
  in
  helper [] n |> List.rev
;;

let is_exp var = String.starts_with ~prefix:"2**" var

let get_exp var =
  assert (is_exp var);
  String.sub var 3 (String.length var - 3)
;;

let decide_order vars =
  let rec perms list =
    let a =
      if List.length list <> 0
      then
        List.mapi
          (fun i el ->
             let list = List.filteri (fun j _ -> i <> j) list in
             List.map (fun list' -> el :: list') (perms list))
          list
        |> List.concat
      else [ [] ]
    in
    a
  in
  let perms = perms (Map.keys vars) in
  perms
  |> List.filter (fun perm ->
    Base.List.for_alli
      ~f:(fun i var ->
        if is_exp var
        then (
          let x = get_exp var in
          List.find_index (fun y -> x = y) perm |> Option.value ~default:9999999 > i)
        else true)
      perm)
  |> List.filter (fun perm ->
    Base.List.for_alli
      ~f:(fun exi ex ->
        if is_exp ex
        then (
          let x = get_exp ex in
          match List.find_index (fun x' -> x = x') perm with
          | Some xi ->
            Base.List.for_alli
              ~f:(fun eyi ey ->
                if is_exp ey && eyi > exi
                then (
                  let y = get_exp ey in
                  match List.find_index (fun y' -> y = y') perm with
                  | Some yi -> yi > xi
                  | None -> true)
                else true)
              perm
          | None -> true)
        else true)
      perm)
;;

let nfa_for_exponent2 s var var2 chrob =
  chrob
  |> List.map (fun (a, c) ->
    let old_internal_counter = !internal_counter in
    let a_var = internal s in
    let var2_plus_a = internal s in
    let t = internal s in
    let c_mul_t = internal s in
    Debug.printfln "nfa_for_exponent2: internal_counter=%d" !internal_counter;
    Debug.printfln "[ var2_plus_a; c_mul_t; t ] = [%d; %d; %d]" var2_plus_a c_mul_t t;
    let nfa =
      Nfa.project
        [ var2_plus_a; c_mul_t; t; a_var ]
        (Nfa.intersect
           (NfaCollection.add ~lhs:var2_plus_a ~rhs:c_mul_t ~res:var)
           (Nfa.intersect
              (Nfa.intersect
                 (NfaCollection.add ~res:var2_plus_a ~lhs:var2 ~rhs:a_var)
                 (NfaCollection.eq_const a_var a))
              (NfaCollection.mul ~res:c_mul_t ~lhs:c ~rhs:t)))
    in
    Debug.dump_nfa ~msg:"nfa_for_exponent2 output nfa: %s" Nfa.format_nfa nfa;
    internal_counter := old_internal_counter;
    nfa)
;;

let _ = nfa_for_exponent2

let nfa_for_exponent s var newvar chrob =
  chrob
  |> List.concat_map (fun (a, c) ->
    if c = 0
    then
      List.init (a + 10) (( + ) a)
      |> List.map (fun x ->
        let log = log2 x in
        x - log, log, 0)
      |> List.filter (fun (t, _, _) -> t = a)
    else c |> gen_list_n |> List.map (fun d -> a, d, c))
  |> List.map (fun (a, d, c) ->
    let old_internal_counter = !internal_counter in
    let a_plus_d = internal s in
    let t = internal s in
    let c_mul_t = internal s in
    let internal = internal s in
    let nfa =
      Nfa.project
        [ a_plus_d; c_mul_t; t ]
        (Nfa.intersect
           (NfaCollection.add ~lhs:a_plus_d ~rhs:c_mul_t ~res:var)
           (Nfa.intersect
              (NfaCollection.eq_const a_plus_d (a + d))
              (NfaCollection.mul ~res:c_mul_t ~lhs:c ~rhs:t)))
    in
    let n =
      List.init (a + 2) (( + ) a) |> List.filter (fun x -> x - log2 x >= a) |> List.hd
    in
    let newvar_nfa = NfaCollection.torename newvar d c in
    let geq_nfa =
      NfaCollection.geq var internal |> Nfa.intersect (NfaCollection.eq_const internal n)
    in
    let nfa =
      nfa
      |> Nfa.intersect newvar_nfa
      |> Nfa.minimize
      |> Nfa.intersect geq_nfa
      |> Nfa.project [ internal ]
    in
    internal_counter := old_internal_counter;
    nfa)
;;

let rec remove_leading_quantifiers = function
  | Ast.Exists (_, f) -> remove_leading_quantifiers f
  | _ as f -> f
;;

let%expect_test "Basic remove leading quantifiers" =
  {|ExEyEz z = 15|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> remove_leading_quantifiers
  |> Format.printf "%a" Ast.pp_formula;
  [%expect {| (z = 15) |}]
;;

let%expect_test "Useless quantifier remove" =
  {|z = 15|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> remove_leading_quantifiers
  |> Format.printf "%a" Ast.pp_formula;
  [%expect {| (z = 15) |}]
;;

let project_exp s nfa x next =
  let get_deg = Map.find_exn s.vars in
  let x' = get_exp x in
  if is_exp next
  then
    nfa
    |> Nfa.get_chrobaks_sub_nfas
         ~res:(get_deg x)
         ~temp:(get_deg next)
         ~vars:(Map.data s.vars)
    |> List.to_seq
    |> Seq.flat_map (fun (nfa, chrobak, model_part) ->
      (let y = get_exp next in
       Debug.dump_nfa
         ~msg:"close to nfa_for_exponent2 - intersection nfa: %s"
         Nfa.format_nfa
         nfa;
       nfa_for_exponent2 s (get_deg x') (get_deg y) chrobak)
      |> List.map (Nfa.intersect nfa)
      |> List.map (fun nfa -> nfa, model_part)
      |> List.to_seq)
  else (
    let old_counter = !internal_counter in
    let inter = internal s in
    let ans =
      nfa
      |> Nfa.intersect (NfaCollection.torename2 (get_deg x') inter)
      |> Nfa.get_chrobaks_sub_nfas ~res:(get_deg x) ~temp:inter ~vars:(Map.data s.vars)
      |> List.to_seq
      |> Seq.flat_map (fun (nfa, chrobak, model_part) ->
        nfa_for_exponent s (get_deg x') inter chrobak
        |> List.map (Nfa.intersect nfa)
        |> List.map (fun nfa -> nfa, model_part)
        |> List.to_seq)
      |> Seq.map (fun (nfa, model_part) -> Nfa.project [ inter ] nfa, model_part)
    in
    internal_counter := old_counter;
    ans)
;;

let proof_order return project s nfa order =
  let get_deg = Map.find_exn s.vars in
  let rec helper nfa order model =
    Debug.dump_nfa ~msg:"Nfa inside proof_order: %s" Nfa.format_nfa nfa;
    match order with
    | [] -> return s nfa model
    | x :: [] -> return s (project (get_deg x) nfa) model
    | x :: (next :: _ as tl) ->
      if not (is_exp x)
      then helper (project (get_deg x) nfa) tl model
      else (
        let deg = (Map.max_elt_exn s.vars |> snd) + 2 in
        let x' = get_exp x in
        let zero_nfa =
          Nfa.intersect
            (NfaCollection.eq_const (get_deg x) 1)
            (NfaCollection.eq_const (get_deg x') 0)
          |> Nfa.truncate deg
          |> Nfa.intersect nfa
          |> project (get_deg x)
        in
        Debug.printf "Zero nfa for %s: " x;
        Debug.dump_nfa ~msg:"%s" Nfa.format_nfa zero_nfa;
        match helper zero_nfa tl model with
        | Some _ as res -> res
        | None ->
          project_exp s nfa x next
          |> Seq.map (fun (nfa, model_part) ->
            helper (Nfa.minimize (project (get_deg x) nfa)) tl (model_part :: model))
          |> Seq.find_map Fun.id)
  in
  helper nfa order []
;;

let prepare_order s nfa order =
  Debug.printfln
    "Trying order %a"
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf " <= ")
       Format.pp_print_string)
    (order |> List.rev);
  let len = List.length order in
  let* nfa =
    if len <= 1
    then Ok nfa
    else
      let* order_nfa, order_vars =
        eval
          s
          (Seq.zip
             (order |> List.to_seq |> Seq.take (len - 1))
             (order |> List.to_seq |> Seq.drop 1)
           |> Seq.map (fun (x, y) -> Ast.Geq (Ast.Var x, Ast.Var y))
           |> List.of_seq
           |> function
           | [] -> failwith ""
           | h :: tl -> List.fold_left Ast.mand h tl)
      in
      Debug.printfln
        "order_vars: %a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt (a, b) -> Format.fprintf fmt "%s -> %d" a b))
        (order_vars |> Map.to_alist);
      Debug.printfln
        "s.vars: %a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt (a, b) -> Format.fprintf fmt "%s -> %d" a b))
        (s.vars |> Map.to_alist);
      let order_nfa =
        order_nfa
        |> Nfa.reenumerate
             (order_vars |> Map.map_keys_exn ~f:(fun k -> Map.find_exn s.vars k))
      in
      Nfa.intersect nfa order_nfa |> Nfa.minimize |> Result.ok
  in
  Debug.dump_nfa ~msg:"NFA taking order into account: %s" Nfa.format_nfa nfa;
  (order, nfa) |> return
;;

let eval_semenov return next formula =
  let formula = remove_leading_quantifiers formula in
  (* if
    Ast.for_some
      (function
        | Ast.Any (_, _) | Ast.Exists (_, _) -> true
        | _ -> false)
      (fun _ -> false)
      formula
  then
    Format.printf
      "Semënov arithmetic formula contains quantifiers not on the top-level. In general such \
       formulas might be undecidable. We still try to evaluate them though to try out the \
       limitations of the algorithm.\n\
       %!"; *)
  let* nfa, vars = eval !s formula in
  let nfa = Nfa.minimize nfa in
  let nfa =
    Map.fold
      ~init:nfa
      ~f:(fun ~key:k ~data:v acc ->
        if is_exp k then Nfa.intersect acc (NfaCollection.power_of_two v) else acc)
      vars
  in
  let nfa =
    Map.fold
      ~f:(fun ~key:k ~data:v acc ->
        if is_exp k
        then acc
        else if Map.mem vars ("2**" ^ k) |> not
        then Nfa.project [ v ] acc
        else acc)
      ~init:nfa
      vars
  in
  let nfa = Nfa.minimize nfa in
  Debug.dump_nfa
    ~msg:"Minimized original nfa: %s"
    ~vars:(Map.to_alist vars)
    Nfa.format_nfa
    nfa;
  let powered_vars =
    Map.filteri ~f:(fun ~key:k ~data:_ -> is_exp k || Map.mem vars ("2**" ^ k)) vars
  in
  let s = { !s with vars = powered_vars } in
  decide_order powered_vars
  |> List.to_seq
  |> Seq.map (prepare_order s nfa)
  |> Seq.filter (function
    | Error _ -> true
    | Ok (order, nfa) ->
      nfa
      |> Nfa.project (order |> List.map (fun str -> Map.find_exn s.vars str))
      |> Nfa.run)
  |> Seq.map (Result.map (fun (order, nfa) -> proof_order return next s nfa order))
  |> Seq.find (function
    | Ok (Some _) | Error _ -> true
    | Ok None -> false)
  |> function
  | Some x -> x
  | None -> Ok None
;;

let proof_semenov f =
  f
  |> eval_semenov
       (fun _ nfa _ -> if Nfa.run nfa then Some () else None)
       (fun x nfa -> Nfa.project [ x ] nfa)
  |> Result.map Option.is_some
;;

let get_model_normal f =
  let* nfa, vars = f |> eval !s in
  let free_vars = f |> collect_free |> Set.to_list in
  Nfa.any_path nfa (List.map (fun v -> Map.find_exn vars v) free_vars)
  |> Option.map (fun (model, _) ->
    model |> List.mapi (fun i v -> List.nth free_vars i, v) |> Map.of_alist_exn)
  |> return
;;

let get_model_semenov f =
  let* res =
    f
    |> eval_semenov
         (fun s nfa model ->
            match Nfa.any_path nfa (Map.data s.vars) with
            | Some path -> Some (s, path, model)
            | None -> None)
         (fun _ nfa -> nfa)
  in
  match res with
  | Some (s, model, models) ->
    let rec thing = function
      | [] -> failwith "unreachable"
      | [ (model, _) ] -> model
      | (model, len1) :: (model2, len2) :: tl ->
        ( Base.List.zip_exn model model2
          |> List.map (fun (x, y) ->
            Debug.printfln "x=%d,y=%d,len1=%d,len2=%d" x y len1 len2;
            (y * pow2 len1) + x)
        , len1 + len2 )
        :: tl
        |> thing
    in
    let map =
      thing (model :: models)
      |> List.mapi (fun i v -> List.nth (Map.keys s.vars) i, v)
      |> Map.of_alist_exn
    in
    let map = Map.filter_keys map ~f:(fun key -> not (is_exp key)) in
    let f =
      f
      |> Ast.map Fun.id (function
        | Ast.Var x ->
          Base.Option.value ~default:(Ast.Var x) (Map.find map x |> Option.map Ast.const)
        | Ast.Pow (2, Ast.Const c) -> Ast.Const (pow2 c)
        | Ast.Pow _ as t -> failwith (Format.asprintf "unimplemented: %a" Ast.pp_term t)
        | x -> x)
    in
    let* model = get_model_normal f in
    Map.merge map (Option.get model) ~f:(fun ~key:_ -> function
      | `Left x -> Some x
      | `Right x -> Some x
      | `Both _ -> failwith "Should be unreachable")
    |> Option.some
    |> Result.ok
  | None -> Ok None
;;

let proof f =
  let run_semenov =
    Ast.for_some
      (fun _ -> false)
      (function
        | Ast.Pow (_, _) -> true
        | _ -> false)
      f
  in
  if run_semenov
  then proof_semenov f
  else (
    let f = Optimizer.optimize f in
    Debug.printfln "optimized formula: %a" Ast.pp_formula f;
    let* nfa, _ = f |> eval !s in
    Debug.dump_nfa ~msg:"resulting nfa: %s" Nfa.format_nfa nfa;
    Nfa.run nfa |> return)
;;

let get_model f =
  let run_semenov =
    Ast.for_some
      (fun _ -> false)
      (function
        | Ast.Pow (_, _) -> true
        | _ -> false)
      f
  in
  let* model = if run_semenov then get_model_semenov f else get_model_normal f in
  match model with
  | Some model -> model |> Option.some |> return
  | None -> Option.none |> return
;;

let%expect_test "Proof any x > 7 can be represented as a linear combination of 3 and 5" =
  Format.printf
    "%b"
    ({|AxEyEz x = 3*y + 5*z | x <= 7|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof any x > 6 can be represented as a linear combination of 3 and 5"
  =
  Format.printf
    "%b"
    ({|AxEyEz x = 3*y + 5*z | x <= 6|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof for all x exists x + 1" =
  Format.printf
    "%b"
    ({|AxEy y = x + 1|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof for all x exists x - 1" =
  Format.printf
    "%b"
    ({|AxEy x = y + 1|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof simple existential formula" =
  Format.printf
    "%b"
    ({|ExEy 15 = x + y & y <= 10|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof simple any quantified formula" =
  Format.printf
    "%b"
    ({|Ax x = 2 | ~(x = 2)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof 2 <= 3" =
  Format.printf
    "%b"
    ({|2 <= 3|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof zero is the least" =
  Format.printf
    "%b"
    ({|Ax x >= 0|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof 3 >= 15" =
  Format.printf
    "%b"
    ({|3 >= 15|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof less than 1 is zero" =
  Format.printf
    "%b"
    ({|Ax x < 1 -> x = 0|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof if x > 3 and y > 4 then x + y > 7" =
  Format.printf
    "%b"
    ({|AxAy x > 3 & y > 4 -> x + y > 7|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof two is even" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(2)|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Proof three is odd" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(3)|} |> Parser.parse_formula |> Result.get_ok |> proof |> Result.get_ok);
  s := default_s ();
  [%expect {| false |}]
;;

let%expect_test "Proof sum of two even is even" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|AxAyAz x + y = z & even(x) & even(y) -> even(z)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Proof sum of two even plus one is odd" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|AxAyAz x + y = z & even(x) & even(y) -> ~even(z + 1)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Disproof sum of two even plus one is even" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|AxAyAz x + y = z & even(x) & even(y) -> even(z + 1)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  s := default_s ();
  [%expect {| false |}]
;;

let%expect_test "Proof a number is even iff it's not odd" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  {|Ey x = 2*y + 1|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "odd" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|Ax (even(x) -> ~odd(x)) & (~odd(x) -> even(x))|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Get a model for x = 3 & y = 7" =
  s := default_s ();
  let model =
    {|x = 3 & y = 7|}
    |> Parser.parse_formula
    |> Result.get_ok
    |> get_model
    |> Result.get_ok
    |> Option.get
  in
  Map.iteri ~f:(fun ~key:k ~data:v -> Format.printf "%s = %d  " k v) model;
  s := default_s ();
  [%expect {| x = 3  y = 7 |}]
;;

let%expect_test "Get a model for Ey x = 7*y & x > 9 & x < 20" =
  s := default_s ();
  let model =
    {|Ey x = 7*y & x > 9 & x < 20|}
    |> Parser.parse_formula
    |> Result.get_ok
    |> get_model
    |> Result.get_ok
    |> Option.get
  in
  Map.iteri ~f:(fun ~key:k ~data:v -> Format.printf "%s = %d  " k v) model;
  s := default_s ();
  [%expect {| x = 14 |}]
;;

let%expect_test "Disproof 2**x equals to 0" =
  Format.printf
    "%b"
    ({|2**x = 0|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x equals to 1 if x = 0" =
  Format.printf
    "%b"
    ({|2**x = 1|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof 2**x + 2**y could be less than 2" =
  Format.printf
    "%b"
    ({|2**x + 2**y < 2|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x + 2**y could be less than 3" =
  Format.printf
    "%b"
    ({|2**x + 2**y < 3|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof 2**x equals to 2**x" =
  Format.printf
    "%b"
    ({|2**x = 2**x|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof 2**x equals to 2**y" =
  Format.printf
    "%b"
    ({|2**x = 2**y|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof 2**x equals to x" =
  Format.printf
    "%b"
    ({|2**x = x|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x equals to x + 1 with x = 1" =
  Format.printf
    "%b"
    ({|2**x = x + 1|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof 2**x equals to x + 2 with x = 2" =
  Format.printf
    "%b"
    ({|2**x = x + 2|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof 2**x equals to x + 3" =
  Format.printf
    "%b"
    ({|2**x = x + 3|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x can be equal to 2**y + 1" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 1|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof 2**x can be equal to 2**y + 2" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 2|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof 2**x can be equal to 2**y + 5" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 5|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x can be equal to 2**y + 2**z + 7" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 2**z + 7|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Proof exists even 2**x" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(2**x)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Proof exists odd (not even) 2**x" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|~even(2**x)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Proof not exists odd 2**x having x > 0" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|~even(2**x) & x > 0|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| false |}]
;;

let%expect_test "Proof exists even 2**x + 1" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(2**x + 1)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Proof not exists even 2**x + 1 for x > 0" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(2**x + 1) & x > 0|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| false |}]
;;

let%expect_test "Proof exists an even 2**x" =
  s := default_s ();
  {|Ey x = 2*y|}
  |> Parser.parse_formula
  |> Result.get_ok
  |> pred "even" [ "x" ]
  |> Result.get_ok;
  Format.printf
    "%b"
    ({|even(2**x)|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  s := default_s ();
  [%expect {| true |}]
;;

let%expect_test "Disproof 2**x <= y & y < (2(2**x)) & 2**z <= 5y & 5y < (2(2**z)) & x = z"
  =
  Format.printf
    "%b"
    ({|2**x <= y & y < (2*(2**x)) & 2**z <= 5*y & 5*y < (2*(2**z)) & x = z|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x <= z & z < 2(2**x) & 60 <= z & z <= 100 & ~x = 6 & 5y = z" =
  Format.printf
    "%b"
    ({|2**x <= z & z < 2*(2**x) & 60 <= z & z <= 100 & ~x = 6 & 5*y = z|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test
    "Disproof 2**x <= z & z < 2*(2**x) & 61 <= z & z <= 100 & ~x = 6 & 5*y = z"
  =
  Format.printf
    "%b"
    ({|2**x <= z & z < 2*(2**x) & 61 <= z & z <= 100 & ~x = 6 & 5*y = z|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Disproof 2**x can be equal to 2**y + 5 using common proof" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 5|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof 2**x can be equal to 2**y + 2**z + 7 using common proof" =
  Format.printf
    "%b"
    ({|2**x = 2**y + 2**z + 7|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;

let%expect_test "Disproof quantified 2**x can be equal to 2**y + 5 using common proof" =
  Format.printf
    "%b"
    ({|ExEy 2**x = 2**y + 5|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof_semenov
     |> Result.get_ok);
  [%expect {| false |}]
;;

let%expect_test "Proof quantified 2**x can be equal to 2**y + 2**z + 7 using common proof"
  =
  Format.printf
    "%b"
    ({|ExEy 2**x = 2**y + 2**z + 7|}
     |> Parser.parse_formula
     |> Result.get_ok
     |> proof
     |> Result.get_ok);
  [%expect {| true |}]
;;
