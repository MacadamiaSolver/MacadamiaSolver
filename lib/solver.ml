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

let throw_if cond a = if cond then failwith a
(*let default_s () = { (*preds = []; rpreds = []; *)vars = Map.empty(*; total = 0; progress = 0*) }
let s = ref (default_s ())*)

let internal_counter = ref 0

let internal s =
  internal_counter := !internal_counter + 1;
  !internal_counter - 1 + Map.length s.vars
;;

let collect_vars ir =
  Ir.fold
    (fun acc -> function
       | Ir.Exists (atoms, _) -> Set.union acc (Set.of_list atoms)
       | Ir.Eia
           ( Ir.Eia.Eq (Ir.Eia.Sum term, _)
           | Ir.Eia.Leq (Ir.Eia.Sum term, _)
           | Ir.Eia.Geq (Ir.Eia.Sum term, _)
           | Ir.Eia.Gt (Ir.Eia.Sum term, _)
           | Ir.Eia.Lt (Ir.Eia.Sum term, _) ) ->
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
       | Ir.Eia
           ( Ir.Eia.Eq (Ir.Eia.Sum term, _)
           | Ir.Eia.Leq (Ir.Eia.Sum term, _)
           | Ir.Eia.Geq (Ir.Eia.Sum term, _)
           | Ir.Eia.Gt (Ir.Eia.Sum term, _)
           | Ir.Eia.Lt (Ir.Eia.Sum term, _) ) ->
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
      | Ir.Lnot (Ir.Eia (Ir.Eia.Geq (term, c))) -> Ir.eia (Ir.Eia.lt term c)
      | Ir.Lnot (Ir.Eia (Ir.Eia.Lt (term, c))) -> Ir.eia (Ir.Eia.geq term c)
      | Ir.Lnot (Ir.Eia (Ir.Eia.Gt (term, c))) -> Ir.eia (Ir.Eia.leq term c)
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

  let eval vars ir =
    match ir with
    | ( Eq (Sum term, c)
      | Geq (Sum term, c)
      | Leq (Sum term, c)
      | Lt (Sum term, c)
      | Gt (Sum term, c) ) as ir ->
      Debug.printfln "IR %a" Ir.Eia.pp_ir ir;
      let var_count = Map.length vars in
      let internalc = ref var_count in
      let internal () =
        let var = !internalc in
        internalc := !internalc + 1;
        var
      in
      let lhs_term = Map.filter ~f:(( < ) 0) term in
      let lhs_c = if c < 0 then -c else 0 in
      let rhs_term = Map.filter ~f:(( > ) 0) term |> Map.map ~f:(fun a -> -a) in
      let rhs_c = if c > 0 then c else 0 in
      Debug.printfln "LHS RHS C %d %d" lhs_c rhs_c;
      (* TODO: Speed this stuff up. *)
      let nfa_term_c term c =
        let mul a atom =
          let idx = Map.find_exn vars atom in
          let rec mul = function
            | 0 -> failwith "unreachable"
            | 1 ->
              let ret_idx = internal () in
              ret_idx, NfaCollection.eq ret_idx idx
            | a when a mod 2 = 0 ->
              let idx', nfa' = mul (a / 2) in
              let ret_idx = internal () in
              ( ret_idx
              , NfaCollection.add ~lhs:idx' ~rhs:idx' ~res:ret_idx |> Nfa.intersect nfa' )
            | a ->
              let idx', nfa' = mul (a - 1) in
              let idx'' = internal () in
              let nfa'' = NfaCollection.eq idx'' idx in
              let ret_idx = internal () in
              ( ret_idx
              , NfaCollection.add ~lhs:idx' ~rhs:idx'' ~res:ret_idx
                |> Nfa.intersect nfa'
                |> Nfa.intersect nfa'' )
          in
          mul a
        in
        let atom_nfas =
          Map.mapi ~f:(fun ~key:var ~data:a -> mul a var) term
          |> Map.to_alist
          |> List.map snd
        in
        let idx, nfa =
          match atom_nfas with
          | (idx, nfa) :: tl ->
            List.fold_left
              (fun (idx', nfa') (idx, nfa) ->
                 let idx'' = internal () in
                 let nfa'' =
                   NfaCollection.add ~lhs:idx ~rhs:idx' ~res:idx''
                   |> Nfa.intersect nfa
                   |> Nfa.intersect nfa'
                 in
                 idx'', nfa'')
              (idx, nfa)
              tl
          | [] ->
            let idx = internal () in
            let nfa = NfaCollection.eq_const idx 0 in
            idx, nfa
        in
        if c <> 0
        then (
          let idx' = internal () in
          let nfa' = NfaCollection.eq_const idx' c in
          let res_idx = internal () in
          let nfa =
            NfaCollection.add ~lhs:idx ~rhs:idx' ~res:res_idx
            |> Nfa.intersect nfa
            |> Nfa.intersect nfa'
          in
          res_idx, nfa)
        else idx, nfa
      in
      let lhs_idx, lhs_nfa = nfa_term_c lhs_term lhs_c in
      let rhs_idx, rhs_nfa = nfa_term_c rhs_term rhs_c in
      Debug.dump_nfa ~msg:"dumping ndfa %s" Nfa.format_nfa lhs_nfa;
      Debug.dump_nfa ~msg:"dumping ndfa %s" Nfa.format_nfa rhs_nfa;
      Debug.printf "%d %d" lhs_idx rhs_idx;
      let build_nfa =
        match ir with
        | Eq (_, _) -> NfaCollection.eq
        | Leq (_, _) -> NfaCollection.leq
        | Geq (_, _) -> NfaCollection.geq
        | Lt (_, _) -> NfaCollection.lt
        | Gt (_, _) -> NfaCollection.gt
      in
      build_nfa lhs_idx rhs_idx
      |> Nfa.intersect rhs_nfa
      |> Nfa.intersect lhs_nfa
      |> Nfa.truncate var_count
      |> (fun x ->
      Debug.dump_nfa ~msg:"res %s" Nfa.format_nfa x;
      x)
      |> Nfa.minimize
  ;;
end

module Bv = struct
  open Ir.Bv

  let rec eval_ir vars ir =
    match ir with
    | And terms -> failwith "", failwith ""
    | Or terms -> failwith "", failwith ""
    | Xor (term1, term22) -> failwith "", failwith ""
  ;;

  let eval vars ir =
    let var_count = Map.length vars in
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
  ;;
end

let eval ir =
  let ir = simpl_ir ir in
  let vars = collect_vars ir in
  let rec eval = function
    | Ir.True -> NfaCollection.n ()
    | Ir.Lnot ir -> eval ir |> Nfa.invert
    | Ir.Land (hd :: tl) ->
      List.fold_left (fun nfa ir -> eval ir |> Nfa.intersect nfa) (eval hd) tl
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

let get_model f =
  let () =
    throw_if
      (collect_vars f |> Map.keys |> List.exists is_exp)
      "Semenov arithmetic doesn't support getting a model yet"
  in
  let nfa, vars = eval f in
  let free_vars = f |> collect_free |> Set.to_list in
  let model = Nfa.any_path nfa (List.map (fun v -> Map.find_exn vars v) free_vars) in
  match model with
  | Some model ->
    List.mapi (fun i v -> List.nth free_vars i, v) model
    |> Map.of_alist_exn
    |> Option.some
  | None -> Option.none
;;

let log2 n =
  let rec helper acc = function
    | 0 -> acc
    | n -> helper (acc + 1) (n / 2)
  in
  helper (-1) n
;;

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

let proof_semenov formula =
  (*let formula = failwith "" remove_leading_quantifiers formula in*)
  (*if
    Ast.for_some
      (function
        | Ast.Any (_, _) | Ast.Exists (_, _) -> true
        | _ -> false)
      (fun _ -> false)
      formula
  then
    Format.printf
      "Semenov arithmetic formula contains quantifiers not on the top-level. In general such \
       formulas might be undecidable. We still try to evaluate them though to try out the \
       limitations of the algorithm.\n\
       %!";*)
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
  let s = { vars } in
  let get_deg x = Map.find_exn vars x in
  let powered_vars =
    Map.filteri ~f:(fun ~key:k ~data:_ -> is_exp k || Map.mem vars (to_exp k)) vars
  in
  let orders = decide_order powered_vars in
  let rec proof_order nfa order =
    match order with
    | [] -> nfa |> Nfa.run
    | x :: tl ->
      Debug.dump_nfa ~msg:"Nfa inside proof_order: %s" Nfa.format_nfa nfa;
      (match is_exp x with
       | false -> proof_order (Nfa.project [ get_deg x ] nfa) tl
       | true ->
         (match List.length tl with
          | 0 -> nfa |> Nfa.project [ get_deg x ] |> Nfa.run
          | _ ->
            let deg () = Map.length s.vars in
            let old_counter = !internal_counter in
            let inter = internal s in
            let next = List.nth tl 0 in
            let temp = if is_exp next then get_deg next else inter in
            let x' = get_exp x in
            let zero_nfa =
              Nfa.intersect
                (NfaCollection.eq_const (Map.find_exn s.vars x) 1)
                (NfaCollection.eq_const (Map.find_exn s.vars x') 0)
              |> Nfa.truncate (deg ())
            in
            let zero_nfa =
              nfa |> Nfa.intersect zero_nfa |> Nfa.project [ Map.find_exn s.vars x ]
            in
            Debug.printf "Zero nfa for %a: " Ir.pp_atom x;
            Debug.dump_nfa ~msg:"%s" Nfa.format_nfa zero_nfa;
            if proof_order zero_nfa tl
            then true
            else (
              let nfa =
                if is_exp next
                then nfa
                else nfa |> Nfa.intersect (NfaCollection.torename2 (get_deg x') inter)
              in
              let t = Nfa.get_chrobaks_sub_nfas nfa ~res:(get_deg x) ~temp in
              let result =
                t
                |> List.to_seq
                |> Seq.flat_map (fun (nfa, chrobak) ->
                  let a =
                    (match is_exp next with
                     | false -> nfa_for_exponent s (Map.find_exn s.vars x') inter chrobak
                     | true ->
                       let y = get_exp next in
                       Debug.dump_nfa
                         ~msg:"close to nfa_for_exponent2 - intersection nfa: %s"
                         Nfa.format_nfa
                         nfa;
                       nfa_for_exponent2
                         s
                         (Map.find_exn s.vars x')
                         (Map.find_exn s.vars y)
                         chrobak)
                    |> List.map (Nfa.intersect nfa)
                  in
                  a |> List.to_seq)
                |> Seq.map (Nfa.project [ get_deg x; inter ])
                |> Seq.map (fun nfa -> proof_order (Nfa.minimize nfa) tl)
                |> Seq.exists Fun.id
              in
              internal_counter := old_counter;
              result)))
  in
  orders
  |> List.to_seq
  |> Seq.map (fun order ->
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
          Nfa.reenumerate
            (order_vars |> Map.map_keys_exn ~f:(fun k -> Map.find_exn vars k))
            order_nfa
        in
        Nfa.intersect nfa order_nfa |> Nfa.minimize)
    in
    Debug.dump_nfa ~msg:"NFA taking order into account: %s" Nfa.format_nfa nfa;
    nfa |> Nfa.project (order |> List.map (fun str -> Map.find_exn s.vars str)) |> Nfa.run
    && proof_order nfa order)
  |> Seq.find (fun x -> x)
  |> function
  | Some x -> if x then `Sat else `Unsat
  | None -> `Unsat
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
