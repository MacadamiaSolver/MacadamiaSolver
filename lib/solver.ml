(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

module Set = Base.Set.Poly
module Map = Base.Map.Poly

type t =
  { (*preds : (string * Ir.atom list * Ir.t * Nfa.t * (Ir.atom, int) Map.t) list
  ; rpreds : (string * Regex.t * Nfa.t) list
  ; *)
    vars : (Ir.atom, int) Map.t
    (* total : int
  ; progress : int*)
  }

(* let throw_if cond a = if cond then failwith a *)
(*let default_s () = { (*preds = []; rpreds = []; *)vars = Map.empty(*; total = 0; progress = 0*) }
let s = ref (default_s ())*)

let internal_counter = ref 0

let internal s =
  internal_counter := !internal_counter + 1;
  !internal_counter + (s.vars |> Map.data |> List.fold_left Int.max 0)
;;

let collect_vars ir =
  Ir.fold
    (fun acc -> function
       | Ir.Exists (atoms, _) -> Set.union acc (Set.of_list atoms)
       | Ir.Eia (Ir.Eia.Eq (Ir.Eia.Sum term, _) | Ir.Eia.Leq (Ir.Eia.Sum term, _)) ->
         Set.union acc (Set.of_list (Map.keys term))
       | _ -> acc)
    Set.empty
    ir
  |> Set.to_list
  |> List.mapi (fun i var -> var, i)
  |> Map.of_alist_exn
;;

let collect_free ir =
  Ir.fold
    (fun acc -> function
       | Ir.Eia (Ir.Eia.Eq (Ir.Eia.Sum term, _) | Ir.Eia.Leq (Ir.Eia.Sum term, _)) ->
         Set.union acc (Set.of_list (Map.keys term))
       | Ir.Exists (xs, _) -> Set.diff acc (Set.of_list xs)
       | _ -> acc)
    Set.empty
    ir
;;

let simpl_ir ir =
  let simpl_negation =
    Ir.map (function
      | Ir.Lnot (Ir.Lnot ir) -> ir
      | Ir.Lnot (Ir.Lor irs) -> Ir.land_ (List.map Ir.lnot irs)
      | Ir.Lnot (Ir.Land irs) -> Ir.lor_ (List.map Ir.lnot irs)
      | ir -> ir)
  in
  let simpl_ops =
    Ir.map (function
      | Ir.Lnot (Ir.Eia (Ir.Eia.Leq (term, c))) -> Ir.eia (Ir.Eia.gt term c)
      | ir -> ir)
  in
  let quantifiers_closer =
    Ir.map (function
      | Ir.Exists ([], ir) -> ir
      | Ir.Exists (atoms, Ir.Exists (atoms', ir)) -> Ir.exists (atoms @ atoms') ir
      | Ir.Exists (atoms, (Ir.Land irs as ir')) | Ir.Exists (atoms, (Ir.Lor irs as ir'))
        ->
        let op =
          match ir' with
          | Ir.Land _ -> Ir.land_
          | Ir.Lor _ -> Ir.lor_
          | _ -> assert false
        in
        let atoms_set = atoms |> Set.of_list in
        let irs_using_var =
          List.mapi
            begin
              fun i ir ->
                let free_vars = collect_free ir in
                let used_vars = Set.inter atoms_set free_vars in
                i, used_vars
            end
            irs
        in
        let var_is_used_in =
          List.map
            begin
              fun atom ->
                ( atom
                , List.filter_map
                    (fun (i, s) -> if Set.mem s atom then Some i else None)
                    irs_using_var )
            end
            atoms
          |> Map.of_alist_exn
        in
        let atoms, irs =
          Map.fold
            ~f:
              begin
                fun ~key:atom ~data:used_in (atoms, irs) ->
                  match used_in with
                  | [] -> atoms, irs
                  | [ i ] ->
                    ( atoms
                    , List.mapi
                        (fun j ir -> if i = j then Ir.exists [ atom ] ir else ir)
                        irs )
                  | _ -> atom :: atoms, irs
              end
            ~init:([], irs)
            var_is_used_in
        in
        Ir.exists atoms (op irs)
      | ir -> ir)
  in
  let rec simpl ir =
    let ir' = ir |> simpl_ops |> simpl_negation |> quantifiers_closer in
    Debug.printf "Simplify step: %a\n" Ir.pp ir';
    if Ir.equal ir' ir then ir' else simpl ir'
  in
  simpl ir
  |> fun x ->
  Debug.printf "Simplified expression: %a\n" Ir.pp x;
  x
;;

module Eia = struct
  open Ir.Eia

  let powerset term =
    let rec helper = function
      | [] -> []
      | [ x ] -> [ 0, [ 0 ]; 1, [ x ] ]
      | hd :: tl ->
        let open Base.List.Let_syntax in
        let ( let* ) = ( >>= ) in
        let* n, thing = helper tl in
        [ n, 0 :: thing; n + Int.shift_left 1 (List.length thing), hd :: thing ]
    in
    term
    |> List.map snd
    |> helper
    |> List.map (fun (a, x) -> a, Base.List.sum (module Base.Int) ~f:Fun.id x)
  ;;

  let eval vars ir =
    match ir with
    | Eq (Sum term, c) | Leq (Sum term, c) ->
      let term = Map.map_keys_exn ~f:(Map.find_exn vars) term |> Map.to_alist in
      let thing = powerset term in
      Debug.printfln "IR %a" Ir.Eia.pp_ir ir;
      Debug.printfln
        "thing:[%a]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt (b, c) -> Format.fprintf fmt "(%d, %d)" b c))
        thing;
      let states = ref Set.empty in
      let transitions = ref [] in
      let rec lp front =
        match front with
        | [] -> ()
        | hd :: tl ->
          if Set.mem !states hd
          then lp tl
          else begin
            let t =
              match ir with
              | Eq _ ->
                thing
                |> List.filter (fun (_, sum) -> (hd - sum) mod 2 = 0)
                |> List.map (fun (bits, sum) -> hd, bits, (hd - sum) / 2)
              | Leq _ ->
                thing
                |> List.map (fun (bits, sum) ->
                  ( hd
                  , bits
                  , match (hd - sum) mod 2 with
                    | 0 | 1 -> (hd - sum) / 2
                    | -1 -> ((hd - sum) / 2) - 1
                    | _ -> failwith "Should be unreachable" ))
            in
            Debug.printfln
              "hd:%d, t:[%a]"
              hd
              (Format.pp_print_list
                 ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
                 (fun fmt (a, b, c) -> Format.fprintf fmt "(%d, %d, %d)" a b c))
              t;
            states := Set.add !states hd;
            transitions := t @ !transitions;
            lp (List.map (fun (_, _, x) -> x) t @ tl)
          end
      in
      lp [ c ];
      let states = Set.to_list !states in
      Debug.printfln
        "states:[%a]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt a -> Format.fprintf fmt "%d" a))
        states;
      let states = states |> List.mapi (fun i x -> x, i) |> Map.of_alist_exn in
      let idx c = Map.find states c |> Option.get in
      let transitions = List.map (fun (a, b, c) -> idx a, b, idx c) !transitions in
      Nfa.create_nfa
        ~transitions
        ~start:[ idx c ]
        ~final:
          (match ir with
           | Eq _ -> [ idx 0 ]
           | Leq _ -> states |> Map.filter_keys ~f:(fun x -> x >= 0) |> Map.data)
        ~vars:(List.map fst term)
        ~deg:(1 + List.fold_left Int.max 0 (List.map fst term))
      |> fun x ->
      Debug.dump_nfa ~msg:"Build (L)Eq Nfa: %s" ~vars:(Map.to_alist vars) Nfa.format_nfa x;
      x
  ;;
end

module Bv = struct
  (*open Ir.Bv*)

  (*
     let rec eval_ir vars ir =
    match ir with
    | And terms -> failwith "", failwith ""
    | Or terms -> failwith "", failwith ""
    | Xor (term1, term22) -> failwith "", failwith ""
  ;;*)

  let eval _vars _ir =
    (*let var_count = Map.length vars in
    match ir with
    | (Eq [ lhs; rhs ] | Geq (lhs, rhs) | Leq (lhs, rhs) | Lt (lhs, rhs) | Gt (lhs, rhs))
      as ir ->
      let lhs_idx, lhs_nfa = eval_ir vars lhs in
      let rhs_idx, rhs_nfa = eval_ir vars rhs in
      let build_nfa =
        match ir with
        | Eq _ -> NfaCollection.eq
        | Leq (_, _) -> NfaCollection.leq
        | Geq (_, _) -> NfaCollection.geq
        | Lt (_, _) -> NfaCollection.lt
        | Gt (_, _) -> NfaCollection.gt
      in
      build_nfa lhs_idx rhs_idx
      |> Nfa.intersect rhs_nfa
      |> Nfa.intersect lhs_nfa
      |> Nfa.truncate var_count
    *)
    failwith "unimplemented"
  ;;
end

let eval ir =
  let ir = simpl_ir ir in
  let vars = collect_vars ir in
  let rec eval = function
    | Ir.True -> NfaCollection.n ()
    | Ir.Lnot ir -> eval ir |> Nfa.invert
    (*
       | Ir.Land (hd :: tl) ->
      List.fold_left (fun nfa ir -> eval ir |> Nfa.intersect nfa) (eval hd) tl
    *)
    | Ir.Land irs ->
      let nfas =
        List.map eval irs
        |> List.sort (fun nfa1 nfa2 -> Nfa.length nfa1 - Nfa.length nfa2)
      in
      let rec eval_and = function
        | hd :: [] -> hd
        | hd :: hd' :: tl ->
          let nfas =
            Nfa.intersect hd hd' :: tl
            |> List.sort (fun nfa1 nfa2 -> Nfa.length nfa1 - Nfa.length nfa2)
          in
          eval_and nfas
        | [] -> failwith ""
      in
      eval_and nfas
    | Ir.Lor (hd :: tl) ->
      List.fold_left (fun nfa ir -> eval ir |> Nfa.unite nfa) (eval hd) tl
    | Ir.Eia eia_ir -> Eia.eval vars eia_ir
    | Ir.Bv bv_ir -> Bv.eval vars bv_ir
    | Ir.Exists (atoms, ir) ->
      eval ir |> Nfa.project (List.map (Map.find_exn vars) atoms) |> Nfa.minimize
    | Ir.Pred _ -> failwith "fuck"
    | _ -> Format.asprintf "Unsupported IR %a to evaluate to" Ir.pp ir |> failwith
  in
  eval ir
  |> fun x ->
  Debug.dump_nfa ~msg:"evaluating %s" Nfa.format_nfa x;
  x, vars
;;

let dump f =
  let nfa, _ = eval f in
  Format.asprintf "%a" Nfa.format_nfa (nfa |> Nfa.minimize)
;;

let is_exp = function
  | Ir.Pow2 _ -> true
  | Ir.Var _ | Ir.Internal _ -> false
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

let get_exp = function
  | Ir.Pow2 var -> Ir.var var
  | Ir.Var _ | Ir.Internal _ -> failwith "Expected exponent, found var"
;;

let to_exp = function
  | Ir.Pow2 _ -> failwith "Expected var"
  | Ir.Var var | Ir.Internal var -> Ir.pow2 var
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

(*
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
*)

let project_exp s nfa x next =
  Debug.dump_nfa ~msg:"Nfa inside project_exp: %s" Nfa.format_nfa nfa;
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
    let nfa = nfa |> Nfa.intersect (NfaCollection.torename2 (get_deg x') inter) in
    Debug.dump_nfa ~msg:"Nfa intersected with torename2: %s" Nfa.format_nfa nfa;
    let ans =
      nfa
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
        Debug.printf "Zero nfa for %a: " Ir.pp_atom x;
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
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " <= ") Ir.pp_atom)
    (order |> List.rev);
  let len = List.length order in
  let nfa =
    if len <= 1
    then nfa
    else (
      let order_nfa, order_vars =
        eval
          (Seq.zip
             (order |> List.to_seq |> Seq.take (len - 1))
             (order |> List.to_seq |> Seq.drop 1)
           |> Seq.map (fun (x, y) ->
             let term = [ x, 1; y, -1 ] |> Map.of_alist_exn in
             Ir.Eia (Ir.Eia.geq (Ir.Eia.sum term) 0))
           |> List.of_seq
           |> function
           | [] -> failwith ""
           | comps -> Ir.land_ comps)
      in
      let order_nfa =
        order_nfa
        |> Nfa.reenumerate
             (order_vars |> Map.map_keys_exn ~f:(fun k -> Map.find_exn s.vars k))
      in
      Nfa.intersect nfa order_nfa |> Nfa.minimize)
  in
  Debug.dump_nfa ~msg:"NFA taking order into account: %s" Nfa.format_nfa nfa;
  order, nfa
;;

let eval_semenov return next formula =
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
  let vars = collect_vars formula in
  let formula =
    formula
    |> (fun ir ->
    Ir.exists
      (vars
       |> Map.keys
       |> List.filter (fun var -> (not (is_exp var)) && not (Map.mem vars (to_exp var))))
      ir)
    |> simpl_ir
  in
  let nfa, vars = eval formula in
  let nfa = Nfa.minimize nfa in
  Debug.dump_nfa
    ~msg:"Minimized raw original nfa: %s"
    ~vars:(Map.to_alist vars)
    Nfa.format_nfa
    nfa;
  let nfa =
    Map.fold
      ~init:nfa
      ~f:(fun ~key:k ~data:v acc ->
        if is_exp k then Nfa.intersect acc (NfaCollection.power_of_two v) else acc)
      vars
  in
  Debug.dump_nfa
    ~msg:"Minimized raw2 original nfa: %s"
    ~vars:(Map.to_alist vars)
    Nfa.format_nfa
    nfa;
  let nfa =
    Map.fold
      ~f:(fun ~key:k ~data:v acc ->
        if is_exp k
        then acc
        else if Map.mem vars (to_exp k) |> not
        then Nfa.project [ v ] acc
        else acc)
      ~init:nfa
      vars
  in
  Debug.dump_nfa
    ~msg:"Minimized raw3 original nfa: %s"
    ~vars:(Map.to_alist vars)
    Nfa.format_nfa
    nfa;
  let nfa = Nfa.minimize nfa in
  Debug.dump_nfa
    ~msg:"Minimized original nfa: %s"
    ~vars:(Map.to_alist vars)
    Nfa.format_nfa
    nfa;
  let powered_vars =
    Map.filteri ~f:(fun ~key:k ~data:_ -> is_exp k || Map.mem vars (to_exp k)) vars
  in
  let s = { vars = powered_vars } in
  decide_order powered_vars
  |> List.to_seq
  |> Seq.map (prepare_order s nfa)
  |> Seq.filter (function order, nfa ->
      nfa
      |> Nfa.project (order |> List.map (fun str -> Map.find_exn s.vars str))
      |> Nfa.run)
  |> Seq.map (fun (order, nfa) -> proof_order return next s nfa order)
  |> Seq.find (function
    | Some _ -> true
    | None -> false)
  |> function
  | Some x -> x
  | None -> None
;;

let proof_semenov f =
  match
    f
    |> eval_semenov
         (fun _ nfa _ -> if Nfa.run nfa then Some () else None)
         (fun x nfa -> Nfa.project [ x ] nfa)
  with
  | Some _ -> `Sat
  | None -> `Unsat
;;

let get_model_normal f =
  let nfa, vars = f |> eval in
  let free_vars = f |> collect_free |> Set.to_list in
  Nfa.any_path nfa (List.map (fun v -> Map.find_exn vars v) free_vars)
  |> Option.map (fun (model, _) ->
    model |> List.mapi (fun i v -> List.nth free_vars i, v) |> Map.of_alist_exn)
;;

let get_model_semenov f =
  let res =
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
      |> Ir.map (function
        | Ir.Bv _ -> failwith "unimplemented"
        | Ir.Eia eia ->
          eia
          |> Ir.Eia.map_ir (fun (Sum term) c ->
            let filter =
              fun k ->
              match k with
              | Ir.Pow2 _ -> true
              | Ir.Var _ -> Map.mem map k
              | Ir.Internal _ -> failwith "Unexpected"
            in
            let c =
              term
              |> Map.filter_keys ~f:filter
              |> Map.to_sequence
              |> Base.Sequence.map ~f:(fun (k, v) ->
                v
                *
                  match k with
                  | Ir.Pow2 x -> pow2 (Map.find_exn map (Ir.Var x))
                  | Ir.Var _ -> Map.find_exn map k
                  | Ir.Internal _ -> failwith "Unexpected")
              |> Base.Sequence.fold ~init:c ~f:( + )
            in
            let term = term |> Map.filter_keys ~f:(Fun.negate filter) in
            Sum term, c)
          |> Ir.eia
        (* | Ast.Var x -> *)
        (*   Base.Option.value ~default:(Ast.Var x) (Map.find map x |> Option.map Ast.const) *)
        (* | Ast.Pow (2, Ast.Const c) -> Ast.Const (pow2 c) *)
        (* | Ast.Pow _ as t -> failwith (Format.asprintf "unimplemented: %a" Ast.pp_term t) *)
        | x -> x)
    in
    let model = get_model_normal f in
    Map.merge map (Option.get model) ~f:(fun ~key:_ -> function
      | `Left x -> Some x
      | `Right x -> Some x
      | `Both _ -> failwith "Should be unreachable")
    |> Option.some
  | None -> None
;;

let proof ir =
  let run_semenov = collect_vars ir |> Map.keys |> List.exists is_exp in
  if run_semenov
  then proof_semenov ir
  else (
    (*let f = Optimizer.optimize f in
    Debug.printfln "optimized formula: %a" Ast.pp_formula f;*)
    let free_vars = collect_free ir in
    let ir = Ir.exists (free_vars |> Set.to_list) ir in
    let nfa, _ = ir |> eval in
    Debug.dump_nfa ~msg:"resulting nfa: %s" Nfa.format_nfa nfa;
    if Nfa.run nfa then `Sat else `Unsat)
;;

let get_model f =
  let run_semenov = collect_vars f |> Map.keys |> List.exists is_exp in
  if run_semenov then get_model_semenov f else get_model_normal f
;;

(*
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
*)
