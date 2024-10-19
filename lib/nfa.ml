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

let get_extended_final_states transitions final =
  let reversed_transitions =
    transitions
    |> Map.map
         ~f:
           (Set.filter_map ~f:(fun (map, state) ->
                if map |> Map.for_all ~f:(( = ) Bits.O) then Some state
                else None ) )
    |> Map.to_sequence
    |> Sequence.concat_map ~f:(fun (source, targets) ->
           targets |> Set.to_sequence
           |> Sequence.map ~f:(fun target -> (target, source)) )
    |> Map.of_sequence_multi |> Map.map ~f:Set.of_list
  in
  let rec helper acc = function
    | [] ->
        acc
    | h :: tl ->
        if Set.mem acc h then helper acc tl
        else
          let acc = Set.add acc h in
          ( Set.diff
              ( Map.find reversed_transitions h
              |> Base.Option.value ~default:Set.empty )
              acc
          |> Set.to_list )
          @ tl
          |> helper acc
  in
  final |> Set.to_list |> helper Set.empty

let update_final_states_nfa (Nfa nfa) =
  Nfa
    { transitions= nfa.transitions
    ; start= nfa.start
    ; final= nfa.final |> get_extended_final_states nfa.transitions }

let create_nfa ~(transitions : ('s * ('var, bit) Map.t * 's) list)
    ~(start : 's list) ~(final : 's list) =
  Nfa
    { transitions=
        transitions
        |> List.map (fun (a, b, c) -> (a, (b, c)))
        |> Map.of_alist_multi |> Map.map ~f:Set.of_list
    ; final= Set.of_list final
    ; start= Set.of_list start }
  |> update_final_states_nfa

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

let rec reachable_from transitions cur =
  let next =
    cur |> Set.to_sequence
    |> Sequence.map ~f:(fun x ->
           x |> Map.find transitions |> Base.Option.value ~default:Set.empty )
    |> Sequence.to_list |> Set.union_list
  in
  if next |> Set.is_subset ~of_:cur then cur
  else reachable_from transitions @@ Set.union cur next

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
                   transitions
                   |> Map.to_sequence
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
  |> update_final_states_nfa

(*let map_cartesian_product m1 m2 = 
  Map.fold ~f:(fun ~key:a ~data:c x -> 
    Map.fold ~f:(fun ~key:b ~data:d y -> 
      Map.add_exn ~key:(a, b) ~data:(c, d) y)
      ~init:x
      m2)
    ~init:Map.empty
    m1
  Base.Sequence.cartesian_product (Set.to_sequence l1) (Set.to_sequence l2)
  |> Set.of_sequence*)

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
  let reachable = reachable_from transitions nfa.start in
  Nfa
    { start= nfa.start
    ; final= Set.inter nfa.final reachable
    ; transitions=
        nfa.transitions
        |> Map.filter_keys ~f:(Set.mem reachable)
        |> Map.map ~f:(Set.filter ~f:(fun (_, state) -> Set.mem reachable state))
    }

let intersect (Nfa nfa1) (Nfa nfa2) =
  let cartesian_product l1 l2 =
    Set.fold ~f:(fun x a ->
      Set.fold ~f:(fun y b ->
        Set.add y (a, b))
        ~init:x
        l2)
      ~init:Set.empty
      l1 in
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
        |> Map.of_sequence_reduce ~f:Set.union}
  |> remove_unreachable
  |> update_final_states_nfa

let unite (Nfa nfa1) (Nfa nfa2) =
  let start =
    Set.union
      (Set.map ~f:(fun q -> (Option.some q, Option.none)) nfa1.start)
      (Set.map ~f:(fun q -> (Option.none, Option.some q)) nfa2.start)
  in
  let final =
    Set.union
      (Set.map ~f:(fun q -> (Option.some q, Option.none)) nfa1.final)
      (Set.map ~f:(fun q -> (Option.none, Option.some q)) nfa2.final)
  in
  let transitions =
    Map.merge
      ( Map.to_sequence nfa1.transitions
      |> Sequence.map ~f:(fun (q1, s) ->
             ( (Option.some q1, Option.none)
             , Set.map ~f:(fun (a, q2) -> (a, (Option.some q2, Option.none))) s
             ) )
      |> Map.of_sequence_reduce ~f:Set.union )
      ( Map.to_sequence nfa2.transitions
      |> Sequence.map ~f:(fun (q1, s) ->
             ( (Option.none, Option.some q1)
             , Set.map ~f:(fun (a, q2) -> (a, (Option.none, Option.some q2))) s
             ) )
      |> Map.of_sequence_reduce ~f:Set.union )
      ~f:(fun ~key:_ data ->
        match data with
          | `Left a ->
              Some a
          | `Right a ->
              Some a
          | `Both _ ->
              assert false )
  in
  Nfa {start; final; transitions} |> update_final_states_nfa

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

let update_final_states_dfa (Dfa dfa) =
  Dfa
    { transitions= dfa.transitions
    ; start= dfa.start
    ; final= dfa.final |> get_extended_final_states dfa.transitions }

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
    Ok
      ( Dfa {transitions; final= Set.of_list final; start}
      |> update_final_states_dfa )
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

let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []

let rec pow a = function
  | 0 ->
      1
  | 1 ->
      a
  | n ->
      let b = pow a (n / 2) in
      b * b * if n mod 2 = 0 then 1 else a

let labels_differ l1 l2 =
  Map.existsi
    ~f:(fun ~key:k1 ~data:v1 ->
      Map.existsi ~f:(fun ~key:k2 ~data:v2 -> k1 = k2 && v1 != v2) l2 )
    l1

let labels_same l1 l2 = labels_differ l1 l2 |> not

let to_dfa (Nfa nfa) =
  let rec aux mqs transitions =
    match mqs with
      | [] ->
          transitions
      | qs :: mqs -> (
        match Map.find transitions qs with
          | Some _ ->
              aux mqs transitions
          | None ->
              let vars =
                Set.fold ~f:Set.union ~init:Set.empty
                  (Set.map
                     ~f:(fun q ->
                       let dq =
                         Map.find nfa.transitions q
                         |> Option.value ~default:Set.empty
                       in
                       Set.fold ~f:Set.union ~init:Set.empty
                         (Set.map
                            ~f:(fun (labels, _) ->
                              Map.keys labels |> Set.of_list )
                            dq ) )
                     qs )
                |> Set.to_list
              in
              let possible =
                0 -- (pow 2 (List.length vars) - 1)
                |> List.map (fun i ->
                       List.fold_right
                         (fun (x, y) -> Map.add_exn ~key:x ~data:y)
                         (List.mapi
                            (fun j x ->
                              ( x
                              , match (1 lsl j) land i with
                                  | 0 ->
                                      Bits.O
                                  | _ ->
                                      Bits.I ) )
                            vars )
                         Map.empty )
              in
              let ndq =
                List.map
                  (fun d ->
                    ( d
                    , Set.fold ~f:Set.union ~init:Set.empty
                        (Set.map
                           ~f:(fun q ->
                             let dq =
                               Map.find nfa.transitions q
                               |> Option.value ~default:Set.empty
                             in
                             Set.filter_map
                               ~f:(fun (labels, q') ->
                                 match labels_same labels d with
                                   | true ->
                                       Option.some q'
                                   | false ->
                                       Option.none )
                               dq )
                           qs ) ) )
                  possible
                |> Set.of_list
              in
              let nqs' = Set.map ~f:snd ndq |> Set.to_list in
              let transitions' = Map.add_exn ~key:qs ~data:ndq transitions in
              aux (List.append nqs' mqs) transitions' )
  in
  let transitions = aux [nfa.start] Map.empty in
  let final =
    List.filter_map
      (fun q ->
        match Set.are_disjoint q nfa.final with
          | true ->
              Option.none
          | false ->
              Option.some q )
      (transitions |> Map.keys)
    |> Set.of_list
  in
  Dfa {final; start= nfa.start; transitions}

let minimize (Dfa dfa) =
  let states =
    [dfa.final; Set.singleton dfa.start; Map.keys dfa.transitions |> Set.of_list]
    @ (Map.data dfa.transitions |> List.map (Set.map ~f:snd))
    |> Set.union_list
  in
  let contains s v =
    Set.find ~f:(fun u -> Stdlib.compare v u = 0) s |> Option.is_some
  in
  (*let rec aux m =
    let m' = Set.fold
      ~f:(fun acc qs -> 
        let qd = Set.map ~f:(fun q1 ->
          Set.filter_map ~f:(fun q2 -> 
            let d1 =
              Option.value (Map.find dfa.transitions q1) ~default:Set.empty
            in
            let d2 =
              Option.value (Map.find dfa.transitions q2) ~default:Set.empty
            in
            match Set.exists
              ~f:(fun (l1, q1') ->
                Set.exists
                  ~f:(fun (l2, q2') ->
                    labels_differ l1 l2 |> not
                  && Map.find_exn m (q1', q2') )
                d2 )
              d1 with
            | true -> Option.some (q1, q2)
            | false -> Option.none)
            qs)
          qs in
        let qs' = Set.map qd
      )
      Set.empty
      m
    in
    match Set.count m' = Set.count m with 
    | true -> m'
    | false -> aux m' in*)
  let rec aux m =
    let m1 =
      Map.mapi
        ~f:(fun ~key:(q1, q2) ~data:v ->
          match v with
            | true ->
                true
            | false ->
                let d1 =
                  Option.value (Map.find dfa.transitions q1) ~default:Set.empty
                in
                let d2 =
                  Option.value (Map.find dfa.transitions q2) ~default:Set.empty
                in
                (*Stdlib.compare q1 q2 != 0
                && *)Set.exists
                     ~f:(fun (l1, q1') ->
                       Set.exists
                         ~f:(fun (l2, q2') ->
                           labels_differ l1 l2 |> not
                           && Map.find_exn m (q1', q2') )
                         d2 )
                     d1 )
        m
    in
    match Map.equal (fun v1 v2 -> v1 = v2) m1 m with
      | true ->
          m1
      | false ->
          aux m1
  in
  let m =
    Set.fold
      ~f:(fun acc (k, v) -> Map.add_exn acc ~key:k ~data:v)
      ~init:Map.empty
      ( Set.map
          ~f:(fun q1 ->
            Set.map
              ~f:(fun q2 ->
                ((q1, q2), contains dfa.final q1 != contains dfa.final q2) )
              states )
          states
      |> Set.fold ~f:(fun acc s -> Set.union acc s) ~init:Set.empty )
    |> aux
  in
  let _ = Set.map ~f:(fun x -> assert (Map.find_exn m (x, x) |> not)) states in
  let new_states =
    Set.map
      ~f:(fun q1 ->
        Set.filter ~f:(fun q2 -> Map.find_exn m (q1, q2) |> not) states )
      states
  in
  let new_state state =
    Set.find_exn ~f:(fun x -> contains x state) new_states
  in
  let start = new_state dfa.start in
  let final = Set.map ~f:(fun qf -> new_state qf) dfa.final in
  let transitions =
    dfa.transitions
      |> Map.map ~f:(fun ms -> Set.map ~f:(fun (m, q') -> (m, new_state q')) ms)
      |> Map.fold
        ~f:(fun ~key:q ~data:v acc ->
          let q' = new_state q in
          match Map.find acc q' with 
          | Some u -> Map.set ~key:q' ~data:(Set.union v u) acc
          | None -> Map.add_exn ~key:q' ~data:v acc)
        ~init:Map.empty
      (*|> Map.map_keys ~f:(fun q -> new_state q)*)
      (*|> Map.map_keys_exn *)
    (*dfa.transitions |> Map.to_sequence
    |> Sequence.map ~f:(fun (q, ms) ->
           let q' = new_state q in
           let ms' = Set.map ~f:(fun (m, q'') -> (m, new_state q'')) ms in
           (q', ms') )
    |> Map.of_sequence_reduce ~f:Set.union*)
  in
  Dfa {start; final; transitions}

let invert (Dfa dfa) =
  let states =
    [dfa.final; Set.singleton dfa.start; Map.keys dfa.transitions |> Set.of_list]
    @ (Map.data dfa.transitions |> List.map (Set.map ~f:snd))
    |> Set.union_list
  in
  let final = Set.diff states dfa.final in
  Dfa {final; start= dfa.start; transitions= dfa.transitions}

let is_graph (Nfa nfa) =
  nfa.transitions
  |> Map.for_all ~f:(Set.for_all ~f:(fun x -> x |> fst |> Map.is_empty))

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
  |> update_final_states_nfa
(*in
  match is_graph nfa with
    | true -> (
      match run_nfa nfa [] with
        | true ->
            nfa_unit () |> to_nfa
        | false ->
            nfa_zero () |> to_nfa )
    | false ->
        nfa*)
