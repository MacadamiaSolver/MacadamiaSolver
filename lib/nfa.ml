open Format
module Set = Base.Set.Poly
module Map = Base.Map.Poly
module Sequence = Base.Sequence

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
    |> Seq.take 5 |> String.of_seq |> Format.fprintf ppf "%s"

  let map _f (vec, mask) _deg =
    (*let vec = Bitv.init (fun n -> ) deg in*)
    (*let mask = Bitv.init (fun n -> ) deg in*)
    return (vec, mask)
  (*let deg (_, mask) = Bitv.length mask*)
end

module Graph = struct
  type t = (Label.t * state) list array

  let verticies (graph : t) = Array.length graph

  let reverse (graph : t) : t =
    let rev_graph = Array.make (verticies graph) [] in
    Array.iteri
      (fun q delta ->
        List.iter
          (fun (label, q') -> rev_graph.(q') <- (label, q) :: rev_graph.(q'))
          delta )
      graph;
    rev_graph
end

type t =
  { transitions: Graph.t
  ; final: state Set.t
  ; start: state Set.t
  ; deg: deg
  ; is_dfa: bool }

let length nfa = Array.length nfa.transitions

let states nfa = 0 -- (length nfa - 1) |> Set.of_list

let reverse_transitions transitions =
  let reversed_transitions = Array.make (Array.length transitions) [] in
  Array.iteri
    (fun q delta ->
      List.iter
        (fun (label, q') ->
          reversed_transitions.(q') <- (label, q) :: reversed_transitions.(q')
          )
        delta )
    transitions;
  reversed_transitions

let remove_unreachable nfa =
  let reversed_transitions = nfa.transitions |> reverse_transitions in
  let reachable =
    let visited = Array.make (length nfa) false in
    let rec bfs reachable = function
      | [] ->
          reachable
      | q :: tl ->
          if visited.(q) then reachable
          else (
            visited.(q) <- true;
            let reachable = Set.add reachable q in
            let delta = Array.get reversed_transitions q in
            let qs = (delta |> List.map snd) @ tl in
            bfs reachable qs )
    in
    bfs Set.empty (nfa.final |> Set.to_list)
  in
  let map_new_old =
    reachable |> Set.to_sequence
    |> Sequence.mapi ~f:(fun v i -> (i, v))
    |> Map.of_sequence_exn
  in
  let map_old_new =
    reachable |> Set.to_sequence
    |> Sequence.mapi ~f:(fun v i -> (v, i))
    |> Map.of_sequence_exn
  in
  let start = nfa.start |> Set.map ~f:(Map.find_exn map_old_new) in
  let final = nfa.final |> Set.map ~f:(Map.find_exn map_old_new) in
  let transitions =
    Array.init (length nfa) (fun q ->
        let old_q = Map.find_exn map_new_old q in
        let delta = nfa.transitions.(old_q) in
        List.filter_map
          (fun (label, old_q') ->
            let q' = Map.find_exn map_old_new old_q' in
            if Set.mem reachable old_q' then Option.some (label, q')
            else Option.none )
          delta )
  in
  {transitions; start; final; deg= nfa.deg; is_dfa= nfa.is_dfa}

let update_final_states_nfa nfa =
  let reversed_transitions = nfa.transitions |> Graph.reverse in
  Printf.printf "\n%!";
  let final =
    let visited = Array.make (length nfa) false in
    let rec bfs reachable = function
      | [] ->
          reachable
      | q :: tl ->
          if visited.(q) then bfs reachable tl
          else (
            visited.(q) <- true;
            let reachable = Set.add reachable q in
            let delta =
              Array.get reversed_transitions q
              |> List.filter (fun (label, _) -> Label.is_zero label)
            in
            let qs = (delta |> List.map snd) @ tl in
            bfs reachable qs )
    in
    bfs Set.empty (nfa.final |> Set.to_list)
  in
  { transitions= nfa.transitions
  ; start= nfa.start
  ; final
  ; deg= nfa.deg
  ; is_dfa= nfa.is_dfa }

let create_nfa ~(transitions : (state * int * state) list) ~(start : state list)
    ~(final : state list) ~(vars : int list) ~(deg : int) =
  let vars = List.rev vars in
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
  { transitions
  ; final= Set.of_list final
  ; start= Set.of_list start
  ; deg
  ; is_dfa= false }
  |> update_final_states_nfa

let create_dfa ~(transitions : (state * int * state) list) ~(start : state)
    ~(final : state list) ~(vars : int list) ~(deg : int) =
  let vars = List.rev vars in
  let max =
    transitions
    |> List.map (fun (fst, _, snd) -> max fst snd)
    |> List.fold_left max 0
  in
  (* TODO: ensure transitions are actually deterministic. *)
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
  { transitions
  ; final= Set.of_list final
  ; start= Set.singleton start
  ; deg
  ; is_dfa= true }

let run nfa = Set.are_disjoint nfa.start nfa.final |> not

let map_labels f nfa =
  let _transitions =
    nfa.transitions
    |> Array.map (fun delta ->
           List.map (fun (label, q') -> (Label.map f label, q')) delta )
  in
  { start= nfa.start
  ; final= nfa.final
  ; transitions= nfa.transitions
  ; deg= nfa.deg
  ; is_dfa= nfa.is_dfa }

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
  let deg = max nfa1.deg nfa2.deg in
  let is_dfa = nfa1.is_dfa && nfa2.is_dfa in
  {final; start; transitions; deg; is_dfa}

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
  {start; final; transitions; deg= nfa1.deg; is_dfa= false}

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
  {final= nfa.final; start= nfa.start; transitions; deg= nfa.deg; is_dfa= false}
  |> update_final_states_nfa

let truncate l nfa =
  let transitions = nfa.transitions in
  Array.iteri
    (fun q delta ->
      let truncate (label, q') = (Label.truncate l label, q') in
      Array.set transitions q (List.map truncate delta) )
    transitions;
  {final= nfa.final; start= nfa.start; transitions; deg= l; is_dfa= false}
  |> update_final_states_nfa

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
      |> List.map (fun (label, q') -> (q', label))
      |> Map.of_alist_multi
      |> Map.iteri ~f:(fun ~key:q' ~data:labels ->
             fprintf ppf "\"%a\" -> \"%a\" [label=\"%a\"]\n" format_state q
               format_state q'
               (Format.pp_print_list
                  ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n")
                  Label.pp_label )
               labels ) )
    nfa.transitions;
  fprintf ppf "}"

let reverse nfa =
  let transitions = Array.make (length nfa) [] in
  Array.iteri
    (fun q delta ->
      List.iter
        (fun (label, q') -> transitions.(q') <- (label, q) :: transitions.(q'))
        delta )
    nfa.transitions;
  {final= nfa.start; start= nfa.final; transitions; deg= nfa.deg; is_dfa= false}

let to_dfa nfa =
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
  {final; start= Set.singleton 0; transitions; deg= nfa.deg; is_dfa= true}

let minimize nfa = nfa |> to_dfa |> reverse |> to_dfa |> reverse |> to_dfa

let invert nfa =
  let dfa = if nfa.is_dfa then nfa else nfa |> to_dfa in
  let states = states dfa in
  let final = Set.diff states dfa.final in
  { final
  ; start= dfa.start
  ; transitions= dfa.transitions
  ; deg= dfa.deg
  ; is_dfa= true }
