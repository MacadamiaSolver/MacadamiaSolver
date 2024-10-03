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
  match combine mask1 mask2 with
    | None ->
        [mask1]
    | Some _ ->
        if Sequence.is_empty (Map.symmetric_diff mask1 mask2 ~data_equal:( = ))
        then [Map.empty]
        else
          let only_right =
            Map.merge mask1 mask2 ~f:(fun ~key:_ data ->
                match data with `Right b -> Some b | _ -> None )
          in
          only_right
          |> Map.fold ~init:[] ~f:(fun ~key ~data:_ acc ->
                 ( only_right
                 |> Map.fold ~init:mask1
                      ~f:(fun
                          ~key:internal_key ~data:internal_data internal_acc ->
                        internal_acc
                        |> Map.add_exn ~key:internal_key
                             ~data:
                               ( if internal_key = key then
                                   match internal_data with
                                     | Bits.O ->
                                         Bits.I
                                     | Bits.I ->
                                         Bits.O
                                 else internal_data ) ) )
                 :: acc )

let make_deterministic (Nfa nfa) =
  let rec multiple_transition_combinations transitions =
    match transitions with
      | [] ->
          []
      | (head_mask, head_state) :: [] ->
          [(head_mask, Set.singleton head_state)]
      | (head_mask, head_state) :: tl ->
          let combs = multiple_transition_combinations tl in
          let combine_trans =
            combs
            |> List.filter_map (fun (mask, multi_state) ->
                   let* comb = combine head_mask mask in
                   Some (comb, Set.add multi_state head_state) )
          in
          let except_trans =
            combs
            |> List.filter_map (fun (mask, multi_state) ->
                   let new_masks =
                     except mask head_mask
                     |> List.filter (fun v -> Map.is_empty v |> not)
                   in
                   if List.is_empty new_masks then None
                   else Some (new_masks, multi_state) )
            |> List.map (fun (l, s) -> List.map (fun v -> (v, s)) l)
            |> List.concat
          in
          let head_trans =
            combs
            |> List.fold_left
                 (fun acc (mask, _) ->
                   List.map (fun v -> except v mask) acc |> List.concat )
                 [head_mask]
            |> List.filter (fun v -> Map.is_empty v |> not)
            |> List.map (fun trans -> (trans, Set.singleton head_state))
          in
          List.concat [combine_trans; except_trans; head_trans]
  in
  let rec helper processed_states states_to_process transitions =
    match states_to_process with
      | [] ->
          (transitions, processed_states)
      | multi_state :: tl ->
          let multi_state_trans =
            Set.map multi_state ~f:(fun state ->
                match Map.find nfa.transitions state with
                  | None ->
                      []
                  | Some a ->
                      a |> Set.to_list )
            |> Set.to_list |> List.concat |> multiple_transition_combinations
          in
          let new_states =
            multi_state_trans
            |> List.fold_left
                 (fun acc (_, multi_state) ->
                   match
                     List.find_opt (Set.equal multi_state)
                       (List.append processed_states states_to_process)
                   with
                     | None ->
                         List.append acc [multi_state]
                     | Some _ ->
                         acc )
                 []
          in
          helper
            (List.append processed_states [multi_state])
            (List.append tl new_states)
            (Map.add_exn transitions ~key:multi_state
               ~data:(multi_state_trans |> Set.of_list) )
  in
  let transitions, states = helper [] [nfa.start] Map.empty in
  Dfa
    { final=
        states
        |> List.filter (fun state -> not (Set.are_disjoint state nfa.final))
        |> Set.of_list
    ; start= nfa.start
    ; transitions }
