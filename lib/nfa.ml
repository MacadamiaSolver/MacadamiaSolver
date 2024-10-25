open Format
open Utils
module Set = Base.Set.Poly
module Map = Base.Map.Poly
module Sequence = Base.Sequence

type bit = Bits.bit
type deg = int
type state = int

let (let*) = Option.bind
let (return) = Option.some

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


let stretch vec mask_list deg =
  let m = mask_list 
    |> List.mapi (fun i k -> (k, Set.singleton i))
    |> Map.of_alist_reduce ~f:(Set.union) in
  let ok = 0--deg
  |> List.for_all (fun j ->
      let js = Map.find m j |> Option.value ~default:Set.empty in
      Set.for_all ~f:(fun j -> Bitv.get vec j) js ||
      Set.for_all ~f:(fun j -> Bitv.get vec j |> not) js) in
  match ok with
  | true ->
    Bitv.init
      deg
      (fun i ->
        (let* js = Map.find m i in
        let* j = Set.nth js 0 in
        let v = Bitv.get vec j in
        match v with 
        | true -> Option.some true
        | false -> Option.none) |> Option.is_some) |> return
  | false -> Option.none

module Label = struct
  type t = Bitv.t * Bitv.t

  let equal (vec1, mask1) (vec2, mask2) =
    let mask = Bitv.bw_and mask1 mask2 in
    Bitv.equal (Bitv.bw_and vec1 mask) (Bitv.bw_and vec2 mask)

  let combine (vec1, mask1) (vec2, mask2) =
    (Bitv.bw_or vec1 vec2, Bitv.bw_or mask1 mask2)

  let project proj (vec, mask) = let len = Bitv.length mask in
    let proj = Bitv.create len true |> Bitv.bw_xor (Bitv.of_list_with_length proj len) in
    (Bitv.bw_and vec proj, Bitv.bw_and mask proj)

  let truncate len (vec, mask) =
    (Bitv.init 32 (fun i -> i < len && Bitv.get vec i), Bitv.init 32 (fun i -> i < len && Bitv.get mask i))

  let is_zero (vec, mask) = Bitv.bw_and vec mask |> Bitv.all_zeros

  let variations (_, mask) = 
    let mask_list = mask |> Bitv.to_list in
    0 -- (pow 2 (List.length mask_list) - 1)
    |> List.map Bitv.of_int_us
    |> List.map (fun x -> stretch x mask_list (Bitv.length mask) |> Option.get)
    |> List.map (fun x -> (x, mask))

  let z deg = (Bitv.init 32 (fun _ -> false), Bitv.init 32 (fun _ -> false))

  let pp_label ppf (vec, mask) =
    Format.fprintf ppf "%a %a" Bitv.L.print vec Bitv.L.print mask

  let deg (_, mask) = Bitv.length mask
end

type t =
      { transitions: (Label.t * state) list array
      ; final: state Set.t
      ; start: state Set.t
      ; deg: deg}

let length nfa = Array.length nfa.transitions
let states nfa = 0--(length nfa - 1) |> Set.of_list

let get_extended_final_states transitions final =
  let reversed_transitions =
    transitions
    |> Map.map
         ~f:
           (Set.filter_map ~f:(fun (label, state) ->
                if Label.is_zero label then Some state
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

let update_final_states_nfa nfa =
  { transitions= nfa.transitions
  ; start= nfa.start
  ; final= nfa.final (*|> get_extended_final_states nfa.transitions*)
  ; deg = nfa.deg}

let create_nfa ~(transitions : (int * state) list list)
    ~(start : state list) ~(final : state list) ~(vars : int list) ~(deg : int) =
  let transitions = 
    transitions
      |> List.map (fun (delta) ->
          List.filter_map (fun (label, q') -> 
            let* vec = stretch (Bitv.of_int_us label) vars deg in
            ((vec, Bitv.of_list_with_length vars deg), q') |> return
          ) delta
        )
      |> Array.of_list in
    { transitions=transitions
    ; final= Set.of_list final
    ; start= Set.of_list start;
    deg = deg}
  |> update_final_states_nfa

let run_nfa nfa  =
  Set.are_disjoint nfa.start nfa.final |> not

let map_vars vars nfa =
  {
    start = nfa.start;
    final = nfa.final;
    transitions = nfa.transitions;
    deg = nfa.deg
  }

let array_from_rev_list list =
  let length = List.length list in
  let array = Array.make length [] in
  List.iteri (fun i v -> Array.set array (length - i - 1) v;) list;
  array

let intersect nfa1 nfa2 =
  assert (nfa1.deg = nfa2.deg);
  let cartesian_product l1 l2 =
    Set.fold ~f:(fun x a ->
      Set.fold ~f:(fun y b ->
        Set.add y (a, b))
        ~init:x
        l2)
      ~init:Set.empty
      l1 in
  let counter = ref (0) in
  let visited = Array.make_matrix (length nfa1) (length nfa2) (-1) in
  let q (q1, q2) = visited.(q1).(q2) in
  let is_visited (q1, q2) = (q (q1, q2)) <> (-1) in
  let visit (q1, q2) = 
    if is_visited (q1, q2) |> not then
    (visited.(q1).(q2) <- !counter; 
    counter := !counter + 1;) in
  let rec aux transitions queue =
    if Queue.is_empty queue then transitions
    else
      let (q1, q2) = Queue.pop queue in
      let delta1 = nfa1.transitions.(q1) in
      let delta2 = nfa2.transitions.(q2) in
      let delta = List.fold_left (fun acc_delta (label1, q1') ->
        List.fold_left (fun acc_delta (label2, q2') -> 
          let equal = Label.equal label1 label2 in
          match equal with
          | true ->
            let label = Label.combine label1 label2 in
            let is_visited = is_visited (q1', q2') in
            visit (q1', q2');
            let q' = q (q1', q2') in
            let acc_delta = (label, q') :: acc_delta in
            if (is_visited |> not) then Queue.add (q1', q2') queue;
            acc_delta
          | false -> acc_delta)
        acc_delta delta2)
      [] delta1 in
      delta :: aux transitions queue in
  let start_pairs = cartesian_product nfa1.start nfa2.start in
  let queue = Queue.create () in
  Set.iter ~f:(fun x -> visit x; Queue.add x queue) start_pairs;
  let transitions = aux [] queue |> Array.of_list in
  let start = start_pairs |> Set.map ~f:q in
  let final = cartesian_product nfa1.final nfa2.final |> Set.map ~f:q in
  { final= final
  ; start= start
  ; transitions= transitions
  ; deg = nfa1.deg }

let unite nfa1 nfa2 =
  assert (nfa1.deg = nfa2.deg);
  let s1 q = q in
  let s2 q = length nfa1 + q in
  let start =
    Set.union
      (Set.map ~f:s1 nfa2.start)
      (Set.map ~f:s2 nfa2.start)
  in
  let final =
    Set.union
      (Set.map ~f:s1 nfa1.final)
      (Set.map ~f:s2 nfa2.final)
  in
  let transitions = Array.append nfa1.transitions nfa2.transitions in
  {start; final; transitions; deg= nfa1.deg}

let is_graph nfa = 
  nfa.transitions
  |> Array.for_all (fun delta -> List.for_all (fun (label, _) -> Label.is_zero label) delta)


let project to_remove nfa = nfa
  (*let transitions = nfa.transitions in
  Array.iteri (fun q delta -> 
    let project (label, q') = 
      (Label.project to_remove label, q')
      in
    Array.set transitions q (List.map project delta)
    ) transitions
    { final= nfa.final
    ; start= nfa.start
    ; transitions=
        nfa.transitions
        |> Map.filter_map ~f:(fun set ->
               let set =
                 set |> Set.map ~f:(fun (label, state) -> (Label.project l label, state))
               in
               if Set.is_empty set then None else Some set );
  deg = nfa.deg}
  |> update_final_states_nfa*)

let truncate l nfa = nfa
    (*{ final= nfa.final
    ; start= nfa.start
    ; transitions=
        nfa.transitions
        |> Map.filter_map ~f:(fun set ->
               let set =
                 set |> Set.map ~f:(fun (label, state) -> (Label.truncate l label, state))
               in
               if Set.is_empty set then None else Some set );
    deg = l}
  |> update_final_states_nfa*)

let format_bitmap format_var ppf bitmap =
  let format_bit ppf = function
    | Bits.O ->
        fprintf ppf "0"
    | Bits.I ->
        fprintf ppf "1"
  in
  Map.iteri bitmap ~f:(fun ~key ~data ->
      fprintf ppf "%a=%a\\n" format_var key format_bit data )

let format_nfa ppf nfa =
  let states = states nfa in
  let format_state ppf state =
    fprintf ppf "%d" (state)
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
  Array.iteri (fun q delta ->
    delta
      |> List.iter (fun (label, q') ->
             fprintf ppf "\"%a\" -> \"%a\" [label=\"%a\"]\n" format_state q
               format_state q' Label.pp_label label ) ) nfa.transitions;
  fprintf ppf "}"

type dfa =
      { transitions: (Label.t * state) list array
      ; final: state Set.t
      ; start: state
      ; deg: int }

let update_final_states_dfa dfa =
  { transitions= dfa.transitions
  ; start= dfa.start
  ; final= dfa.final (*|> get_extended_final_states dfa.transitions *)
  ; deg= dfa.deg}

let to_nfa dfa =
  ({ final= dfa.final
  ; start= Set.singleton dfa.start
  ; transitions= dfa.transitions
  ; deg= dfa.deg} : t)

let to_dfa (nfa : t) =
  ({ final= nfa.final
  ; start= 0
  ; transitions= nfa.transitions
  ; deg= nfa.deg} : dfa)
  (*let rec aux mqs transitions =
    match mqs with
      | [] ->
          transitions
      | qs :: mqs -> (
        match Map.find transitions qs with
          | Some _ ->
              aux mqs transitions
          | None ->
              let acc = 
                Set.fold ~f:(fun acc label -> Label.combine acc label) ~init:(Label.z nfa.deg)
                  (Set.map
                     ~f:(fun q ->
                       let dq =
                         Map.find nfa.transitions q
                         |> Option.value ~default:Set.empty
                       in
                       Set.fold ~f:(fun acc (label, _) -> Label.combine acc label) ~init:(Label.z nfa.deg) dq)
                     qs )
              in
      (*Map.find nfa.transitions qs |> Option.value ~default:Set.empty |> Set.map ~f:fst |> Set.fold ~f:Label.combine ~init:(Label.z ()) in*)
              let variations = Label.variations acc in
              let ndq =
                List.map
                  (fun label ->
                    ( label
                    , Set.fold ~f:Set.union ~init:Set.empty
                        (Set.map
                           ~f:(fun q ->
                             let dq =
                               Map.find nfa.transitions q
                               |> Option.value ~default:Set.empty
                             in
                             Set.filter_map
                               ~f:(fun (label', q') ->
                                 match Label.equal label' label with
                                   | true ->
                                       Option.some q'
                                   | false ->
                                       Option.none )
                               dq )
                           qs ) ) )
                  variations
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
  {final; start= nfa.start; transitions; deg =nfa.deg}*)

let minimize dfa = dfa
  (*let states = states dfa in
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
                  Array.get dfa.transitions q1
                in
                let d2 =
                  Array.get dfa.transitions q1
                in
                Array.exists
                   (fun (l1, q1') ->
                     Array.exists
                       (fun (l2, q2') ->
                         Label.equal l1 l2
                         && Map.find_exn m (q1', q2') )
                       d2)
                   d1)
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
  in
  Dfa {start; final; transitions; deg = dfa.deg }*)

let invert dfa = dfa
  (*let states = states dfa in
  let final = Set.diff states dfa.final in
  {final; start= dfa.start; transitions= dfa.transitions; deg = dfa.deg}*)

