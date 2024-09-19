open Format
open Utils
module Set = Base.Set.Poly
module Map = Base.Map.Poly
module Sequence = Base.Sequence

type bit = Bits.bit

type _ nfa =
  | Nfa :
      { transitions: ('state, (('var, bit) Map.t * 'state) Set.t) Map.t
      ; final: 'state Set.t
      ; start: 'state Set.t }
      -> 'var nfa

let create_nfa ~(transitions : ('s * ('var, bit) Map.t * 's) list)
    ~(start : 's list) ~(final : 's list) =
  Nfa
    { transitions=
        transitions
        |> List.map (fun (a, b, c) -> (a, (b, c)))
        |> Map.of_alist_multi |> Map.map ~f:Set.of_list
    ; final= Set.of_list final
    ; start= Set.of_list start }

let matches (mask : ('a, 'b) Map.t) (map : ('a, 'b) Map.t) : bool =
  Map.fold2 mask map ~init:true ~f:(fun ~key ~data acc ->
      let _ = key in
      acc
      &&
      match data with
        | `Left _ ->
            false
        | `Right _ ->
            true
        | `Both (a, b) ->
            a = b )

let run_nfa (Nfa nfa) str =
  let rec helper str states =
    match str with
      | [] ->
          Set.are_disjoint states nfa.final |> not
      | h :: tl ->
          states |> Set.to_list
          |> List.map (fun state ->
                 Map.find nfa.transitions state
                 |> Base.Option.value ~default:Set.empty
                 |> Set.filter_map ~f:(fun (mask, state) ->
                        if matches mask h then Some state else None ) )
          |> Set.union_list |> helper tl
  in
  helper str nfa.start

let ( let* ) = Option.bind

let map_varname f (Nfa nfa) =
  Nfa
    { final= nfa.final
    ; start= nfa.start
    ; transitions=
        Map.map nfa.transitions
          ~f:
            (Set.filter_map ~f:(fun (transitions, state) ->
                 let* transitions =
                   transitions |> Map.to_sequence
                   |> Sequence.map ~f:(fun (a, b) -> (f a, b))
                   |> Map.of_sequence_multi
                   |> Map.map ~f:(function
                        | [] ->
                            None
                        | h :: tl ->
                            if tl |> List.for_all (( = ) h) then Some h
                            else None )
                   |> option_map_to_map_option
                 in
                 Some (transitions, state) ) ) }

let cartesian_product l1 l2 =
  Base.Sequence.cartesian_product (Set.to_sequence l1) (Set.to_sequence l2)
  |> Set.of_sequence

let combine mask1 mask2 =
  Map.merge mask1 mask2 ~f:(fun ~key data ->
      let _ = key in
      Some
        ( match data with
          | `Left a ->
              Some a
          | `Right a ->
              Some a
          | `Both (a, b) ->
              if a = b then Some a else None ) )
  |> option_map_to_map_option

let remove_unreachable (Nfa nfa) =
  let transitions = nfa.transitions |> Map.map ~f:(Set.map ~f:snd) in
  let rec reachable_from cur =
    let next =
      cur |> Set.to_sequence
      |> Sequence.map ~f:(fun x ->
             x |> Map.find transitions |> Base.Option.value ~default:Set.empty )
      |> Sequence.to_list |> Set.union_list
    in
    if next |> Set.is_subset ~of_:cur then cur
    else reachable_from @@ Set.union cur next
  in
  let reachable = reachable_from nfa.start in
  Nfa
    { start= nfa.start
    ; final= Set.inter nfa.final reachable
    ; transitions=
        nfa.transitions
        |> Map.filter_keys ~f:(Set.mem reachable)
        |> Map.map ~f:(Set.filter ~f:(fun (_, state) -> Set.mem reachable state))
    }

let intersect (Nfa nfa1) (Nfa nfa2) =
  Nfa
    { final= cartesian_product nfa1.final nfa2.final
    ; start= cartesian_product nfa1.start nfa2.start
    ; transitions=
        Base.Sequence.cartesian_product
          (Map.to_sequence nfa1.transitions)
          (Map.to_sequence nfa2.transitions)
        |> Base.Sequence.filter_map ~f:(fun ((src1, list1), (src2, list2)) ->
               let set =
                 cartesian_product list1 list2
                 |> Set.filter_map ~f:(fun ((mask1, state1), (mask2, state2)) ->
                        let* mask = combine mask1 mask2 in
                        Some (mask, (state1, state2)) )
               in
               if Set.is_empty set then None else Some ((src1, src2), set) )
        |> Map.of_sequence_reduce ~f:Set.union }

let project f (Nfa nfa) =
  Nfa
    { final= nfa.final
    ; start= nfa.start
    ; transitions=
        nfa.transitions
        |> Map.filter_map ~f:(fun set ->
               let set =
                 set
                 |> Set.map ~f:(fun (mask, state) ->
                        let mask = Map.filter_keys mask ~f in
                        (mask, state) )
               in
               if Set.is_empty set then None else Some set ) }

let format_bitmap format_var ppf bitmap =
  let format_bit ppf = function
    | Bits.O ->
        fprintf ppf "0"
    | Bits.I ->
        fprintf ppf "1"
  in
  Map.iteri bitmap ~f:(fun ~key ~data ->
      fprintf ppf "%a=%a\\n" format_var key format_bit data )

let format_nfa format_var ppf (Nfa nfa) =
  let format_bitmap = format_bitmap format_var in
  let states =
    [nfa.final; nfa.start; Map.keys nfa.transitions |> Set.of_list]
    @ (Map.data nfa.transitions |> List.map (Set.map ~f:snd))
    |> Set.union_list
  in
  let int_of_state =
    states |> Set.to_list |> List.mapi (fun a b -> (b, a)) |> Map.of_alist_exn
  in
  let format_state ppf state =
    fprintf ppf "%d" (Map.find_exn int_of_state state)
  in
  let states = Set.diff states nfa.final in
  let states = Set.diff states nfa.start in
  let start_final = Set.inter nfa.start nfa.final in
  let start = Set.diff nfa.start start_final in
  let final = Set.diff nfa.final start_final in
  fprintf ppf "digraph {\n";
  Set.iter states ~f:(fprintf ppf "\"%a\" [shape=circle]\n" format_state);
  Set.iter final ~f:(fprintf ppf "\"%a\" [shape=doublecircle]\n" format_state);
  Set.iter start ~f:(fprintf ppf "\"%a\" [shape=octagon]\n" format_state);
  Set.iter start_final
    ~f:(fprintf ppf "\"%a\" [shape=doubleoctagon]\n" format_state);
  Map.iteri nfa.transitions ~f:(fun ~key ~data ->
      data
      |> Set.iter ~f:(fun (bitmap, dst) ->
             fprintf ppf "\"%a\" -> \"%a\" [label=\"%a\"]\n" format_state key
               format_state dst format_bitmap bitmap ) );
  fprintf ppf "}"

type _ dfa =
  | Dfa :
      { transitions: ('state, (('var, bit) Map.t * 'state) Set.t) Map.t
      ; final: 'state Set.t
      ; start: 'state }
      -> 'var dfa

let _subsets set =
  let rec helper acc = function
    | [] ->
        acc
    | h :: tl ->
        helper (acc @ List.map (fun x -> h :: x) acc) tl
  in
  set |> Set.elements |> helper [[]] |> List.map Set.of_list |> Set.of_list

let check_maps_collisions map1 map2 =
  Map.fold2 map1 map2 ~init:true ~f:(fun ~key ~data acc ->
      let _ = key in
      acc
      &&
      match data with
        | `Left _ ->
            true
        | `Right _ ->
            true
        | `Both (a, b) ->
            a = b )

let transitions_collisions transitions =
  Map.to_sequence transitions
  |> Sequence.concat_map ~f:(fun (state, maps) ->
         let maps = maps |> Set.to_sequence in
         Sequence.cartesian_product maps maps
         |> Sequence.filter ~f:(fun ((b1, s1), (b2, s2)) ->
                s1 != s2 && check_maps_collisions b1 b2 )
         |> Sequence.map ~f:(fun ((a, s1), (b, s2)) -> (state, a, b, s1, s2)) )
  |> Sequence.to_list

type ('state, 'varname) dfaCollisions =
  ('state * ('varname, bit) Map.t * ('varname, bit) Map.t * 'state * 'state)
  list

let create_dfa ~(transitions : ('s * ('var, bit) Map.t * 's) list) ~(start : 's)
    ~(final : 's list) =
  let transitions =
    transitions
    |> List.map (fun (a, b, c) -> (a, (b, c)))
    |> Map.of_alist_multi |> Map.map ~f:Set.of_list
  in
  let collisions = transitions_collisions transitions in
  if List.is_empty collisions then
    Ok (Dfa {transitions; final= Set.of_list final; start})
  else Error collisions

let run_dfa (Dfa dfa) str =
  let rec helper str state =
    match str with
      | [] ->
          Set.mem dfa.final state
      | h :: tl -> (
        match
          Map.find dfa.transitions state
          |> Base.Option.value ~default:Set.empty
          |> Set.filter_map ~f:(fun (mask, state) ->
                 if matches mask h then Some state else None )
          |> Set.to_list
        with
          | [] ->
              false
          | [state] ->
              helper tl state
          | _ ->
              failwith "non-deterministic" )
  in
  helper str dfa.start

let to_nfa (Dfa dfa) =
  Nfa
    { final= dfa.final
    ; start= Set.singleton dfa.start
    ; transitions= dfa.transitions }

let except mask1 mask2 =
  Map.merge mask1 mask2 ~f:(fun ~key data ->
      let _ = key in
      Some
        ( match data with
          | `Left a ->
              Some a
          | `Right (a : bit) ->
              Some (match a with Bits.O -> Bits.I | Bits.I -> Bits.O)
          | `Both (a, b) ->
              if a = b then Some a else None ) )
  |> option_map_to_map_option

let make_deterministic (Nfa nfa) =
  let collisions =
    transitions_collisions nfa.transitions
    |> List.filter_map (fun (a, trans1, trans2, dst1, dst2) ->
           let* collision = combine trans1 trans2 in
           let* new_trans1 = except trans1 collision in
           let* new_trans2 = except trans2 collision in
           Some
             ( a
             , ( collision
               , [(trans1, new_trans1, dst1); (trans2, new_trans2, dst2)] ) ) )
    |> Map.of_alist_multi
    |> Map.map ~f:Map.of_alist_multi
    |> Map.map ~f:(Map.map ~f:(fun x -> x |> List.concat |> Set.of_list))
  in
  let new_nodes_in_transitions =
    collisions
    |> Map.map ~f:(fun x ->
           x |> Map.to_alist
           |> List.map (fun (collision, dsts) ->
                  (collision, Set.map dsts ~f:(fun (_, _, dst) -> dst)) )
           |> Set.of_list )
    |> Map.to_alist
    |> List.map (fun (state, trans) -> (Set.singleton state, trans))
    |> Map.of_alist_exn
  in
  let old_nodes_edge_replacements =
    collisions
    |> Map.map ~f:(fun x ->
           x |> Map.to_alist
           |> List.map (fun (_, dsts) -> dsts |> Set.to_list)
           |> List.concat |> Set.of_list )
  in
  let new_states =
    new_nodes_in_transitions
    |> Map.fold ~init:Set.empty ~f:(fun ~key:_ ~data acc ->
           data
           |> Set.fold ~init:acc ~f:(fun acc (_, state) -> Set.add acc state) )
  in
  let transitions =
    old_nodes_edge_replacements
    |> Map.fold ~init:nfa.transitions
         ~f:(fun ~key:repl_key ~data:repl_set repl_acc ->
           repl_set
           |> Set.fold ~init:repl_acc
                ~f:(fun acc (repl_mask, repl, repl_state) ->
                  Map.change acc repl_key ~f:(fun s ->
                      let* s = s in
                      Some
                        ( s
                        |> Set.map ~f:(fun (mask, state) ->
                               if mask = repl_mask && state = repl_state then
                                 (repl, state)
                               else (mask, state) ) ) ) ) )
    (*nfa.transitions |> Map.map ~f:(fun ) |> Map.to_alist
      |> List.map (fun (key, value) -> (Set.singleton key, value))
      |> Map.of_alist_exn
      |> Map.map ~f:(Set.map ~f:(fun (mask, state) -> (mask, Set.singleton state)))*)
    (*добавить new_nodes_in_transitions и добавить переходы из new_states*)
  in
  create_dfa [] [] []
