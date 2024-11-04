open Format
module Set = Base.Set.Poly
module Map = Base.Map.Poly
module Sequence = Base.Sequence

type bit = Bits.bit

type deg = int

type state = int

let ( let* ) = Option.bind

let return = Option.some

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
  let m =
    mask_list
    |> List.mapi (fun i k -> (k, Set.singleton i))
    |> Map.of_alist_reduce ~f:Set.union
  in
  let ok =
    0 -- deg
    |> List.for_all (fun j ->
           let js = Map.find m j |> Option.value ~default:Set.empty in
           Set.for_all ~f:(fun j -> Bitv.get vec j) js
           || Set.for_all ~f:(fun j -> Bitv.get vec j |> not) js )
  in
  match ok with
    | true ->
        Bitv.init deg (fun i ->
            (let* js = Map.find m i in
             let* j = Set.nth js 0 in
             let v = Bitv.get vec j in
             match v with true -> Option.some true | false -> Option.none )
            |> Option.is_some )
        |> return
    | false ->
        Option.none

module Label = struct
  type t = Bitv.t * Bitv.t

  let equal (vec1, mask1) (vec2, mask2) =
    let mask = Bitv.bw_and mask1 mask2 in
    Bitv.equal (Bitv.bw_and vec1 mask) (Bitv.bw_and vec2 mask)

  let combine (vec1, mask1) (vec2, mask2) =
    (Bitv.bw_or vec1 vec2, Bitv.bw_or mask1 mask2)

  let project proj (vec, mask) =
    let len = Bitv.length mask in
    let proj =
      Bitv.create len true |> Bitv.bw_xor (Bitv.of_list_with_length proj len)
    in
    (Bitv.bw_and vec proj, Bitv.bw_and mask proj)

  let truncate len (vec, mask) =
    ( Bitv.init 32 (fun i -> i < len && Bitv.get vec i)
    , Bitv.init 32 (fun i -> i < len && Bitv.get mask i) )

  let is_zero (vec, mask) = Bitv.bw_and vec mask |> Bitv.all_zeros

  let variations (_, mask) =
    let mask_list = mask |> Bitv.to_list in
    0 -- (pow 2 (List.length mask_list) - 1)
    |> List.map Bitv.of_int_us
    |> List.map (fun x -> stretch x mask_list (Bitv.length mask) |> Option.get)
    |> List.map (fun x -> (x, mask))

  let z _ = (Bitv.init 32 (fun _ -> false), Bitv.init 32 (fun _ -> false))

  let pp_label ppf (vec, mask) =
    let vec = Bitv.L.to_string vec |> String.to_seq in
    let mask = Bitv.L.to_string mask |> String.to_seq in
    Seq.zip vec mask
    |> Seq.map (function _, '0' -> '_' | x, _ -> x)
    |> String.of_seq |> Format.fprintf ppf "%s"

  (*let deg (_, mask) = Bitv.length mask*)
end

module Graph = struct
  type t = (Label.t * state) list array

  let reachable_in_range (graph : t) first last (init : state Set.t) =
    assert (first <= last);
    let diff = last - first + 1 in
    let rec helper n cur =
      match n with
        | 0 ->
            ([cur], 1)
        | n ->
            let states =
              cur |> Set.to_sequence
              |> Sequence.concat_map ~f:(fun state ->
                     graph.(state) |> Sequence.of_list |> Sequence.map ~f:snd )
              |> Set.of_sequence
            in
            let next, amount = helper (n - 1) states in
            if amount < diff then (states :: next, amount + 1)
            else (next, amount)
    in
    helper last init |> fst

  let rec reachable (graph : t) (start : state Set.t) : state Set.t =
    let next =
      start |> Set.to_sequence
      |> Sequence.concat_map ~f:(fun i ->
             graph.(i) |> List.map snd |> Sequence.of_list )
      |> Set.of_sequence
    in
    let next = Set.diff next start in
    if Set.is_empty next then start else reachable graph (Set.union start next)

  let reverse (graph : t) : t =
    graph |> Array.to_list
    |> List.mapi (fun src list ->
           list |> List.map (fun (lbl, dst) -> (src, lbl, dst)) )
    |> List.concat
    |> List.fold_left
         (fun lists (dst, lbl, src) ->
           lists.(src) <- (lbl, dst) :: lists.(src);
           lists )
         (Array.init (Array.length graph) (Fun.const []))

  let union_list (graphs : t list) : t =
    match graphs with
      | [] ->
          Array.init 0 (Fun.const [])
      | hd :: tl ->
          let len = Array.length hd in
          tl |> List.iter (fun graph -> assert (Array.length graph = len));
          let res = Array.init len (Fun.const []) in
          0 -- pred len
          |> List.iter (fun i ->
                 res.(i) <- graphs |> List.concat_map (fun graph -> graph.(i)) );
          res
end

type t = {transitions: Graph.t; final: state Set.t; start: state Set.t; deg: deg}

let length nfa = Array.length nfa.transitions

let states nfa = 0 -- (length nfa - 1) |> Set.of_list

let get_extended_final_states transitions final =
  let reversed_transitions = Array.make (Array.length transitions) [] in
  Array.iteri
    (fun q delta ->
      List.iter
        (fun (label, q') ->
          if Label.is_zero label then
            reversed_transitions.(q') <- q :: reversed_transitions.(q') )
        delta )
    transitions;
  let rec helper acc = function
    | [] ->
        acc
    | q :: tl ->
        if Set.mem acc q then helper acc tl
        else
          let acc = Set.add acc q in
          ( Set.diff (Array.get reversed_transitions q |> Set.of_list) acc
          |> Set.to_list )
          @ tl
          |> helper acc
  in
  final |> Set.to_list |> helper Set.empty

let update_final_states_nfa nfa =
  { transitions= nfa.transitions
  ; start= nfa.start
  ; final= nfa.final |> get_extended_final_states nfa.transitions
  ; deg= nfa.deg }

let create_nfa ~(transitions : (state * int * state) list) ~(start : state list)
    ~(final : state list) ~(vars : int list) ~(deg : int) =
  let max =
    transitions
    |> List.map (fun (fst, _, snd) -> max fst snd)
    |> List.fold_left max 0
  in
  let transitions =
    transitions
    |> List.fold_left
         (fun lists (src, lbl, dst) ->
           lists.(src) <- (lbl, dst) :: lists.(src);
           lists )
         (Array.init (max + 1) (Fun.const []))
    |> Array.map (fun delta ->
           List.filter_map
             (fun (label, q') ->
               let* vec = stretch (Bitv.of_int_us label) vars deg in
               ((vec, Bitv.of_list_with_length vars deg), q') |> return )
             delta )
  in
  {transitions; final= Set.of_list final; start= Set.of_list start; deg}
  |> update_final_states_nfa

let run_nfa nfa = Set.are_disjoint nfa.start nfa.final |> not

(*let map_vars _ nfa =
  { start= nfa.start
  ; final= nfa.final
  ; transitions= nfa.transitions
  ; deg= nfa.deg }*)

let intersect nfa1 nfa2 =
  assert (nfa1.deg = nfa2.deg);
  let cartesian_product l1 l2 =
    Set.fold
      ~f:(fun x a -> Set.fold ~f:(fun y b -> Set.add y (a, b)) ~init:x l2)
      ~init:Set.empty l1
  in
  let counter = ref 0 in
  let visited = Array.make_matrix (length nfa1) (length nfa2) (-1) in
  let q (q1, q2) = visited.(q1).(q2) in
  let is_visited (q1, q2) = q (q1, q2) <> -1 in
  let visit (q1, q2) =
    if is_visited (q1, q2) |> not then (
      visited.(q1).(q2) <- !counter;
      counter := !counter + 1 )
  in
  let rec aux transitions queue =
    if Queue.is_empty queue then transitions
    else
      let q1, q2 = Queue.pop queue in
      let delta1 = nfa1.transitions.(q1) in
      let delta2 = nfa2.transitions.(q2) in
      let delta =
        List.fold_left
          (fun acc_delta (label1, q1') ->
            List.fold_left
              (fun acc_delta (label2, q2') ->
                let equal = Label.equal label1 label2 in
                match equal with
                  | true ->
                      let label = Label.combine label1 label2 in
                      let is_visited = is_visited (q1', q2') in
                      visit (q1', q2');
                      let q' = q (q1', q2') in
                      let acc_delta = (label, q') :: acc_delta in
                      if is_visited |> not then Queue.add (q1', q2') queue;
                      acc_delta
                  | false ->
                      acc_delta )
              acc_delta delta2 )
          [] delta1
      in
      delta :: aux transitions queue
  in
  let start_pairs = cartesian_product nfa1.start nfa2.start in
  let queue = Queue.create () in
  Set.iter ~f:(fun x -> visit x; Queue.add x queue) start_pairs;
  let transitions = aux [] queue |> Array.of_list in
  let start = start_pairs |> Set.map ~f:q in
  let final =
    cartesian_product nfa1.final nfa2.final
    |> Set.map ~f:q
    |> Set.filter ~f:(( <> ) (-1))
  in
  {final; start; transitions; deg= nfa1.deg}

let unite nfa1 nfa2 =
  assert (nfa1.deg = nfa2.deg);
  let s1 q = q in
  let s2 q = length nfa1 + q in
  let start = Set.union (Set.map ~f:s1 nfa1.start) (Set.map ~f:s2 nfa2.start) in
  let final = Set.union (Set.map ~f:s1 nfa1.final) (Set.map ~f:s2 nfa2.final) in
  let transitions =
    Array.append
      ( nfa1.transitions
      |> Array.map (fun delta ->
             List.map (fun (label, q') -> (label, s1 q')) delta ) )
      ( nfa2.transitions
      |> Array.map (fun delta ->
             List.map (fun (label, q') -> (label, s2 q')) delta ) )
  in
  {start; final; transitions; deg= nfa1.deg}

let is_graph nfa =
  nfa.transitions
  |> Array.for_all (fun delta ->
         List.for_all (fun (label, _) -> Label.is_zero label) delta )

let project to_remove nfa =
  let transitions = nfa.transitions in
  Array.iteri
    (fun q delta ->
      let project (label, q') = (Label.project to_remove label, q') in
      Array.set transitions q (List.map project delta) )
    transitions;
  {final= nfa.final; start= nfa.start; transitions; deg= nfa.deg}
  |> update_final_states_nfa

let truncate l nfa =
  let transitions = nfa.transitions in
  Array.iteri
    (fun q delta ->
      let truncate (label, q') = (Label.truncate l label, q') in
      Array.set transitions q (List.map truncate delta) )
    transitions;
  {final= nfa.final; start= nfa.start; transitions; deg= l}
  |> update_final_states_nfa

(*let format_bitmap format_var ppf bitmap =
  let format_bit ppf = function
    | Bits.O ->
        fprintf ppf "0"
    | Bits.I ->
        fprintf ppf "1"
  in
  Map.iteri bitmap ~f:(fun ~key ~data ->
      fprintf ppf "%a=%a\\n" format_var key format_bit data )*)

let format_nfa ppf nfa =
  let format_state ppf state = fprintf ppf "%d" state in
  let start_final = Set.inter nfa.start nfa.final in
  let start = Set.diff nfa.start start_final in
  let final = Set.diff nfa.final start_final in
  fprintf ppf "digraph {\n";
  fprintf ppf "node [shape=circle]\n";
  Set.iter final ~f:(fprintf ppf "\"%a\" [shape=doublecircle]\n" format_state);
  Set.iter start ~f:(fprintf ppf "\"%a\" [shape=octagon]\n" format_state);
  Set.iter start_final
    ~f:(fprintf ppf "\"%a\" [shape=doubleoctagon]\n" format_state);
  Array.iteri
    (fun q delta ->
      delta
      |> List.iter (fun (label, q') ->
             fprintf ppf "\"%a\" -> \"%a\" [label=\"%a\"]\n" format_state q
               format_state q' Label.pp_label label ) )
    nfa.transitions;
  fprintf ppf "}"

type dfa =
  { transitions: (Label.t * state) list array
  ; final: state Set.t
  ; start: state
  ; deg: int }

(*let update_final_states_dfa dfa =
  { transitions= dfa.transitions
  ; start= dfa.start
  ; final= dfa.final (*|> get_extended_final_states dfa.transitions *)
  ; deg= dfa.deg}*)

let to_nfa dfa : t =
  { final= dfa.final
  ; start= Set.singleton dfa.start
  ; transitions= dfa.transitions
  ; deg= dfa.deg }

let reverse nfa =
  let transitions = Array.make (length nfa) [] in
  Array.iteri
    (fun q delta ->
      List.iter
        (fun (label, q') -> transitions.(q') <- (label, q) :: transitions.(q'))
        delta )
    nfa.transitions;
  ({final= nfa.start; start= nfa.final; transitions; deg= nfa.deg} : t)

let to_dfa (nfa : t) =
  let to_dfa (nfa : t) =
    let counter = ref 0 in
    let rec aux transitions visited final queue =
      if Queue.is_empty queue then (transitions, final)
      else
        let qs = Queue.pop queue in
        let is_visited visited qs = Map.find visited qs |> Option.is_some in
        let visit visited qs =
          if is_visited visited qs |> not then (
            let q = !counter in
            counter := !counter + 1;
            Map.set visited ~key:qs ~data:q )
          else visited
        in
        let visited = visit visited qs in
        let q visited qs = Map.find_exn visited qs in
        let final =
          if Set.are_disjoint nfa.final qs |> not then
            Set.add final (q visited qs)
          else final
        in
        let acc =
          Set.fold
            ~f:(fun acc q ->
              let delta = Array.get nfa.transitions q in
              List.fold_left
                (fun acc (label, _) -> Label.combine acc label)
                (Label.z nfa.deg) delta
              |> Label.combine acc )
            ~init:(Label.z nfa.deg) qs
        in
        let variations = Label.variations acc in
        let delta, visited =
          List.fold_left
            (fun (acc, visited) label ->
              let qs' =
                Set.fold
                  ~f:(fun acc q ->
                    let delta = Array.get nfa.transitions q in
                    let q' =
                      delta
                      |> List.filter (fun (label', _) ->
                             Label.equal label label' )
                      |> List.map snd
                    in
                    List.append q' acc )
                  ~init:[] qs
                |> Set.of_list
              in
              let is_visited = is_visited visited qs' in
              let q visited qs = Map.find_exn visited qs in
              let visited = visit visited qs' in
              let q' = q visited qs' in
              if is_visited |> not then Queue.add qs' queue;
              ((label, q') :: acc, visited) )
            ([], visited) variations
        in
        let delta', final' = aux transitions visited final queue in
        (delta :: delta', final')
    in
    let queue = Queue.create () in
    Queue.add nfa.start queue;
    let transitions, final = aux [] Map.empty Set.empty queue in
    let transitions = Array.of_list transitions in
    ({final; start= 0; transitions; deg= nfa.deg} : dfa)
  in
  nfa |> reverse |> to_dfa |> to_nfa |> reverse |> to_dfa |> to_nfa

let invert nfa =
  let dfa = nfa |> to_dfa in
  let states = states dfa in
  let final = Set.diff states dfa.final in
  ({final; start= dfa.start; transitions= dfa.transitions; deg= dfa.deg} : t)

let find_c_d (nfa : t) (imp : (int, int) Map.t) =
  assert (Set.length nfa.start = 1);
  let n = length nfa in
  let reachable_in_range = Graph.reachable_in_range nfa.transitions in
  let reachable_in n init = reachable_in_range n n init |> List.hd in
  let states = reachable_in (n - 1) nfa.start in
  let states =
    states |> Set.to_sequence
    |> Sequence.filter_map ~f:(fun state ->
           Map.find imp state |> Option.map (fun d -> (state, d)) )
  in
  states
  |> Sequence.concat_map ~f:(fun (state, d) ->
         let first = (n * n) - n - d in
         let last = (n * n) - n - 1 in
         reachable_in_range first last (Set.singleton state)
         |> List.map (fun set -> not (Set.are_disjoint nfa.final set))
         |> Base.List.zip_exn (first -- last)
         |> List.filter snd |> List.map fst
         |> List.map (fun c -> (state, c + n - 1, d))
         |> Sequence.of_list )

let get_exponent_sub_nfa (nfa : t) (res : int) (pow : int) (temp : int) : t =
  let mask = Bitv.init nfa.deg (fun x -> x = res || x = pow || x = temp) in
  let zero_lbl = (Bitv.init nfa.deg (Fun.const false), mask) in
  let res_lbl = (Bitv.init nfa.deg (( = ) res), mask) in
  let pow_lbl = (Bitv.init nfa.deg (( <> ) res), mask) in
  let reversed_transitions = nfa.transitions |> Graph.reverse in
  let end_transitions =
    reversed_transitions
    |> Array.mapi (fun src list ->
           if Set.mem nfa.final src then
             list |> List.filter (fun (lbl, _) -> Label.equal lbl res_lbl)
           else [] )
  in
  let pre_final =
    end_transitions |> Array.to_list |> List.concat |> List.map snd
    |> Set.of_list
  in
  let zero_transitions =
    reversed_transitions
    |> Array.map (List.filter (fun (lbl, _) -> Label.equal lbl zero_lbl))
  in
  let states = Graph.reachable zero_transitions pre_final in
  let start_transitions =
    reversed_transitions
    |> Array.mapi (fun src list ->
           if Set.mem states src then
             list |> List.filter (fun (lbl, _) -> Label.equal lbl pow_lbl)
           else [] )
  in
  let start =
    0 -- Array.length start_transitions
    |> List.filter (fun i -> start_transitions.(i) |> List.is_empty |> not)
    |> Set.of_list
  in
  let transitions =
    Graph.union_list [end_transitions; zero_transitions; start_transitions]
    |> Graph.reverse
  in
  {transitions; final= nfa.final; start; deg= nfa.deg}
