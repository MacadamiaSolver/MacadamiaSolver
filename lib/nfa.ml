(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

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
;;

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * if n mod 2 = 0 then 1 else a
;;

let stretch vec mask_list deg =
  let m =
    mask_list
    |> List.mapi (fun i k -> k, Set.singleton i)
    |> Map.of_alist_reduce ~f:Set.union
  in
  let ok =
    0 -- deg
    |> List.for_all (fun j ->
      let js = Map.find m j |> Option.value ~default:Set.empty in
      Set.for_all ~f:(fun j -> Bitv.get vec j) js
      || Set.for_all ~f:(fun j -> Bitv.get vec j |> not) js)
  in
  match ok with
  | true ->
    Bitv.init deg (fun i ->
      (let* js = Map.find m i in
       let* j = Set.nth js 0 in
       let v = Bitv.get vec j in
       match v with
       | true -> Option.some true
       | false -> Option.none)
      |> Option.is_some)
    |> return
  | false -> Option.none
;;

module Label = struct
  type t = Bitv.t * Bitv.t

  let equal (vec1, mask1) (vec2, mask2) =
    let len = max (Bitv.length mask1) (Bitv.length mask2) in
    let extend v =
      let vl = Bitv.length v in
      assert (vl <= len);
      if vl = len then v else Bitv.append v (Bitv.create (len - vl) false)
    in
    let vec1 = extend vec1 in
    let vec2 = extend vec2 in
    let mask1 = extend mask1 in
    let mask2 = extend mask2 in
    let mask = Bitv.bw_and mask1 mask2 in
    Bitv.equal (Bitv.bw_and vec1 mask) (Bitv.bw_and vec2 mask)
  ;;

  let combine (vec1, mask1) (vec2, mask2) =
    let len = max (Bitv.length mask1) (Bitv.length mask2) in
    let extend v =
      let vl = Bitv.length v in
      assert (vl <= len);
      if vl = len then v else Bitv.append v (Bitv.create (len - vl) false)
    in
    let vec1 = extend vec1 in
    let vec2 = extend vec2 in
    let mask1 = extend mask1 in
    let mask2 = extend mask2 in
    Bitv.bw_or vec1 vec2, Bitv.bw_or mask1 mask2
  ;;

  let project proj (vec, mask) =
    let len = Bitv.length mask in
    let proj = Bitv.create len true |> Bitv.bw_xor (Bitv.of_list_with_length proj len) in
    Bitv.bw_and vec proj, Bitv.bw_and mask proj
  ;;

  let truncate len (vec, mask) =
    ( Bitv.init len (fun i -> if i < Bitv.length vec then Bitv.get vec i else false)
    , Bitv.init len (fun i -> if i < Bitv.length mask then Bitv.get mask i else false) )
  ;;

  let is_zero (vec, mask) = Bitv.bw_and vec mask |> Bitv.all_zeros

  let variations (_, mask) =
    let mask_list = mask |> Bitv.to_list in
    0 -- (pow 2 (List.length mask_list) - 1)
    |> List.map Bitv.of_int_us
    |> List.map (fun x -> stretch x mask_list (Bitv.length mask) |> Option.get)
    |> List.map (fun x -> x, mask)
  ;;

  let z deg = Bitv.init deg (fun _ -> false), Bitv.init deg (fun _ -> false)

  let pp_label ppf (vec, mask) =
    let vec = Bitv.L.to_string vec |> String.to_seq in
    let mask = Bitv.L.to_string mask |> String.to_seq in
    Seq.zip vec mask
    |> Seq.map (function
      | _, '0' -> '_'
      | x, _ -> x)
    |> String.of_seq
    |> Format.fprintf ppf "(%s)"
  ;;

  let reenumerate map (vec, mask) =
    let length =
      max (Bitv.length vec) ((map |> Map.keys |> List.fold_left max min_int) + 1)
    in
    let vec =
      Bitv.init length (fun i ->
        match Map.find map i with
        | Some j -> Bitv.get vec j
        | None -> false)
    in
    let mask =
      Bitv.init length (fun i ->
        match Map.find map i with
        | Some j -> Bitv.get mask j
        | None -> false)
    in
    vec, mask
  ;;
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
           delta)
      graph;
    rev_graph
  ;;

  let reachable_in_range (graph : t) first last (init : state Set.t) =
    assert (first <= last);
    let diff = last - first + 1 in
    let rec helper n cur =
      match n with
      | 0 -> [ cur ], 1
      | n ->
        let states =
          cur
          |> Set.to_sequence
          |> Sequence.concat_map ~f:(fun state ->
            graph.(state) |> Sequence.of_list |> Sequence.map ~f:snd)
          |> Set.of_sequence
        in
        let next, amount = helper (n - 1) states in
        if amount < diff then states :: next, amount + 1 else next, amount
    in
    helper last init |> fst
  ;;

  let rec _reachable (graph : t) (start : state Set.t) : state Set.t =
    let next =
      start
      |> Set.to_sequence
      |> Sequence.concat_map ~f:(fun i -> graph.(i) |> List.map snd |> Sequence.of_list)
      |> Set.of_sequence
    in
    let next = Set.diff next start in
    if Set.is_empty next then start else _reachable graph (Set.union start next)
  ;;

  let find_strongly_connected_components (graph : t) =
    let s = Stack.create () in
    let rev_graph = reverse graph in
    let visited = Array.make (verticies graph) false in
    let dfs1 v =
      let rec dfs1 v =
        if visited.(v) |> not
        then (
          visited.(v) <- true;
          let us = graph.(v) |> List.map snd in
          List.iter (fun u -> if visited.(u) |> not then dfs1 u else ()) us;
          Stack.push v s)
      in
      dfs1 v
    in
    Array.iteri (fun v _ -> dfs1 v) graph;
    let visited = Array.make (verticies graph) false in
    let rec dfs2 v =
      if visited.(v) |> not
      then (
        visited.(v) <- true;
        let us = rev_graph.(v) |> List.map snd in
        v
        :: (List.map (fun u -> if visited.(u) |> not then dfs2 u else []) us
            |> List.concat))
      else []
    in
    Stack.to_seq s
    |> Seq.filter_map (fun v ->
      if visited.(v) |> not then Option.some (dfs2 v) else Option.none)
    |> List.of_seq
  ;;

  let union_list (graphs : t list) : t =
    match graphs with
    | [] -> Array.init 0 (Fun.const [])
    | hd :: tl ->
      let len = Array.length hd in
      tl |> List.iter (fun graph -> assert (Array.length graph = len));
      let res = Array.init len (Fun.const []) in
      0 -- pred len
      |> List.iter (fun i ->
        res.(i) <- graphs |> List.concat_map (fun graph -> graph.(i)));
      res
  ;;

  let find_shortest_cycle (graph : t) (vertex : state) : int =
    let rec helper acc visited cur =
      if Set.is_empty cur
      then 0
      else (
        let acc = acc + 1 in
        let next =
          cur
          |> Set.to_list
          |> List.concat_map (fun x -> graph.(x) |> List.map snd)
          |> Set.of_list
        in
        if Set.mem next vertex
        then acc
        else (
          let visited = Set.union visited cur in
          helper acc visited (Set.diff next visited)))
    in
    helper 0 Set.empty (Set.singleton vertex)
  ;;

  let find_important_verticies graph =
    let components = find_strongly_connected_components graph in
    List.filter_map
      (fun vs ->
         List.nth_opt
           (List.map (fun v -> v, find_shortest_cycle graph v) vs
            |> List.sort (fun x y -> snd x - snd y))
           0)
      components
  ;;
end

type t =
  { transitions : Graph.t
  ; final : state Set.t
  ; start : state Set.t
  ; deg : deg
  ; is_dfa : bool
  }

let length nfa = Array.length nfa.transitions
let states nfa = 0 -- (length nfa - 1) |> Set.of_list

let remove_unreachable nfa =
  let reversed_transitions = nfa.transitions |> Graph.reverse in
  let reachable =
    let visited = Array.make (length nfa) false in
    let rec bfs reachable = function
      | [] -> reachable
      | q :: tl ->
        if visited.(q)
        then bfs reachable tl
        else (
          visited.(q) <- true;
          let reachable = Set.add reachable q in
          let delta = Array.get reversed_transitions q in
          let qs = (delta |> List.map snd) @ tl in
          bfs reachable qs)
    in
    bfs Set.empty (nfa.final |> Set.to_list)
  in
  let map_new_old =
    reachable
    |> Set.to_sequence
    |> Sequence.mapi ~f:(fun i v -> i, v)
    |> Map.of_sequence_exn
  in
  let map_old_new =
    reachable
    |> Set.to_sequence
    |> Sequence.mapi ~f:(fun i v -> v, i)
    |> Map.of_sequence_exn
  in
  let start = nfa.start |> Set.filter_map ~f:(Map.find map_old_new) in
  let final = nfa.final |> Set.filter_map ~f:(Map.find map_old_new) in
  let transitions =
    Array.init (Set.length reachable) (fun q ->
      let old_q = Map.find_exn map_new_old q in
      let delta = nfa.transitions.(old_q) in
      List.filter_map
        (fun (label, old_q') ->
           if Set.mem reachable old_q'
           then (
             let q' = Map.find_exn map_old_new old_q' in
             Option.some (label, q'))
           else Option.none)
        delta)
  in
  { transitions; start; final; deg = nfa.deg; is_dfa = nfa.is_dfa }
;;

let update_final_states_nfa nfa =
  let reversed_transitions = nfa.transitions |> Graph.reverse in
  let final =
    let visited = Array.make (length nfa) false in
    let rec bfs reachable = function
      | [] -> reachable
      | q :: tl ->
        if visited.(q)
        then bfs reachable tl
        else (
          visited.(q) <- true;
          let reachable = Set.add reachable q in
          let delta =
            Array.get reversed_transitions q
            |> List.filter (fun (label, _) -> Label.is_zero label)
          in
          let qs = (delta |> List.map snd) @ tl in
          bfs reachable qs)
    in
    bfs Set.empty (nfa.final |> Set.to_list)
  in
  { transitions = nfa.transitions
  ; start = nfa.start
  ; final
  ; deg = nfa.deg
  ; is_dfa = nfa.is_dfa
  }
;;

let create_nfa
      ~(transitions : (state * int * state) list)
      ~(start : state list)
      ~(final : state list)
      ~(vars : int list)
      ~(deg : int)
  =
  let vars = List.rev vars in
  let max =
    transitions |> List.map (fun (fst, _, snd) -> max fst snd) |> List.fold_left max 0
  in
  let transitions =
    transitions
    |> List.fold_left
         (fun lists (src, lbl, dst) ->
            lists.(src) <- (lbl, dst) :: lists.(src);
            lists)
         (Array.init (max + 1) (Fun.const []))
    |> Array.map (fun delta ->
      List.filter_map
        (fun (label, q') ->
           let* vec = stretch (Bitv.of_int_us label) vars deg in
           ((vec, Bitv.of_list_with_length vars deg), q') |> return)
        delta)
  in
  { transitions
  ; final = Set.of_list final
  ; start = Set.of_list start
  ; deg
  ; is_dfa = false
  }
  |> update_final_states_nfa
;;

let create_dfa
      ~(transitions : (state * int * state) list)
      ~(start : state)
      ~(final : state list)
      ~(vars : int list)
      ~(deg : int)
  =
  let vars = List.rev vars in
  let max =
    transitions |> List.map (fun (fst, _, snd) -> max fst snd) |> List.fold_left max 0
  in
  (* TODO: ensure transitions are actually deterministic. *)
  let transitions =
    transitions
    |> List.fold_left
         (fun lists (src, lbl, dst) ->
            lists.(src) <- (lbl, dst) :: lists.(src);
            lists)
         (Array.init (max + 1) (Fun.const []))
    |> Array.map (fun delta ->
      List.filter_map
        (fun (label, q') ->
           let* vec = stretch (Bitv.of_int_us label) vars deg in
           ((vec, Bitv.of_list_with_length vars deg), q') |> return)
        delta)
  in
  { transitions
  ; final = Set.of_list final
  ; start = Set.singleton start
  ; deg
  ; is_dfa = true
  }
;;

let run nfa = Set.are_disjoint nfa.start nfa.final |> not

let any_path nfa vars =
  let transitions = nfa.transitions in
  let p =
    let visited = Array.make (length nfa) false in
    let rec dfs len q =
      if visited.(q)
      then None
      else if Set.mem nfa.final q
      then Some ([], q, len)
      else (
        visited.(q) <- true;
        let delta = Array.get transitions q in
        let qs = delta |> List.map snd in
        match List.find_map (fun q -> dfs (len + 1) q) qs with
        | Some (path, q', len) ->
          Some ((List.find (fun (_, q'') -> q' = q'') delta |> fst) :: path, q, len)
        | None ->
          visited.(q) <- false;
          None)
    in
    nfa.start |> Set.to_list |> List.find_map (dfs 0)
  in
  match p with
  | Some (p, _, len) ->
    let length = List.length p in
    Some
      ( List.map
          (fun var ->
             Bitv.init length (fun i -> Bitv.get (List.nth p i |> fst) var)
             |> Bitv.to_int_s)
          vars
      , len )
  | None -> None
;;

let intersect nfa1 nfa2 =
  let cartesian_product l1 l2 =
    Set.fold
      ~f:(fun x a -> Set.fold ~f:(fun y b -> Set.add y (a, b)) ~init:x l2)
      ~init:Set.empty
      l1
  in
  let counter = ref 0 in
  let visited = Array.make_matrix (length nfa1) (length nfa2) (-1) in
  let q (q1, q2) = visited.(q1).(q2) in
  let is_visited (q1, q2) = q (q1, q2) <> -1 in
  let visit (q1, q2) =
    if is_visited (q1, q2) |> not
    then (
      visited.(q1).(q2) <- !counter;
      counter := !counter + 1)
  in
  let rec aux transitions queue =
    if Queue.is_empty queue
    then transitions
    else (
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
                  | false -> acc_delta)
               acc_delta
               delta2)
          []
          delta1
      in
      delta :: aux transitions queue)
  in
  let start_pairs = cartesian_product nfa1.start nfa2.start in
  let queue = Queue.create () in
  Set.iter
    ~f:(fun x ->
      visit x;
      Queue.add x queue)
    start_pairs;
  let transitions = aux [] queue |> Array.of_list in
  let start = start_pairs |> Set.map ~f:q in
  let final =
    cartesian_product nfa1.final nfa2.final |> Set.map ~f:q |> Set.filter ~f:(( <> ) (-1))
  in
  let deg = max nfa1.deg nfa2.deg in
  let is_dfa = nfa1.is_dfa && nfa2.is_dfa in
  { final; start; transitions; deg; is_dfa }
;;

let unite nfa1 nfa2 =
  let s1 q = q in
  let s2 q = length nfa1 + q in
  let start = Set.union (Set.map ~f:s1 nfa1.start) (Set.map ~f:s2 nfa2.start) in
  let final = Set.union (Set.map ~f:s1 nfa1.final) (Set.map ~f:s2 nfa2.final) in
  let transitions =
    Array.append
      (nfa1.transitions
       |> Array.map (fun delta -> List.map (fun (label, q') -> label, s1 q') delta))
      (nfa2.transitions
       |> Array.map (fun delta -> List.map (fun (label, q') -> label, s2 q') delta))
  in
  let deg = max nfa1.deg nfa2.deg in
  { start; final; transitions; deg; is_dfa = false }
;;

let is_graph nfa =
  nfa.transitions
  |> Array.for_all (fun delta ->
    List.for_all (fun (label, _) -> Label.is_zero label) delta)
;;

let reenumerate map nfa =
  let transitions =
    nfa.transitions
    |> Array.map (fun delta ->
      List.map (fun (label, q') -> Label.reenumerate map label, q') delta)
  in
  { start = nfa.start
  ; final = nfa.final
  ; transitions
  ; is_dfa = nfa.is_dfa
  ; deg = Map.keys map |> List.fold_left max min_int
  }
;;

let project to_remove nfa =
  let transitions = Array.copy nfa.transitions in
  Array.iteri
    (fun q delta ->
       let project (label, q') = Label.project to_remove label, q' in
       Array.set transitions q (List.map project delta))
    transitions;
  { final = nfa.final; start = nfa.start; transitions; deg = nfa.deg; is_dfa = false }
  |> update_final_states_nfa
;;

let truncate l nfa =
  let transitions = nfa.transitions in
  Array.iteri
    (fun q delta ->
       let truncate (label, q') = Label.truncate l label, q' in
       Array.set transitions q (List.map truncate delta))
    transitions;
  { final = nfa.final; start = nfa.start; transitions; deg = l; is_dfa = false }
  |> update_final_states_nfa
;;

let format_nfa ppf nfa =
  let format_state ppf state = fprintf ppf "%d" state in
  let start_final = Set.inter nfa.start nfa.final in
  let start = Set.diff nfa.start start_final in
  let final = Set.diff nfa.final start_final in
  fprintf ppf "digraph {\n";
  fprintf ppf "node [shape=circle]\n";
  Set.iter final ~f:(fprintf ppf "\"%a\" [shape=doublecircle]\n" format_state);
  Set.iter start ~f:(fprintf ppf "\"%a\" [shape=octagon]\n" format_state);
  Set.iter start_final ~f:(fprintf ppf "\"%a\" [shape=doubleoctagon]\n" format_state);
  Array.iteri
    (fun q delta ->
       delta
       |> List.map (fun (label, q') -> q', label)
       |> Map.of_alist_multi
       |> Map.iteri ~f:(fun ~key:q' ~data:labels ->
         fprintf
           ppf
           "\"%a\" -> \"%a\" [label=\"%a\"]\n"
           format_state
           q
           format_state
           q'
           (Format.pp_print_list
              ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n")
              Label.pp_label)
           labels))
    nfa.transitions;
  fprintf ppf "}"
;;

let reverse nfa =
  let transitions = Array.make (length nfa) [] in
  Array.iteri
    (fun q delta ->
       List.iter
         (fun (label, q') -> transitions.(q') <- (label, q) :: transitions.(q'))
         delta)
    nfa.transitions;
  { final = nfa.start; start = nfa.final; transitions; deg = nfa.deg; is_dfa = false }
;;

let to_dfa nfa =
  if nfa.is_dfa
  then nfa
  else (
    let counter = ref 0 in
    let length = length nfa in
    let visited = Hashtbl.create length in
    let is_visited qs = Hashtbl.mem visited qs in
    let visit qs =
      if is_visited qs |> not
      then (
        let q = !counter in
        counter := !counter + 1;
        Hashtbl.replace visited qs q)
      else ()
    in
    let processed = Hashtbl.create length in
    let is_processed qs = Hashtbl.mem processed qs in
    let process qs =
      if is_processed qs |> not then Hashtbl.replace processed qs true else ()
    in
    let q qs = Hashtbl.find visited qs in
    let rec aux transitions final queue =
      if Queue.is_empty queue
      then transitions, final
      else (
        let qs = Queue.pop queue in
        if is_processed qs |> not
        then (
          visit qs;
          process qs;
          let final =
            if Set.are_disjoint nfa.final qs |> not then Set.add final (q qs) else final
          in
          let acc =
            Set.fold
              ~f:(fun acc q ->
                let delta = Array.get nfa.transitions q in
                List.fold_left
                  (fun acc (label, _) -> Label.combine acc label)
                  (Label.z nfa.deg)
                  delta
                |> Label.combine acc)
              ~init:(Label.z nfa.deg)
              qs
          in
          let variations = Label.variations acc in
          let delta =
            List.fold_left
              (fun acc label ->
                 let qs' =
                   Set.fold
                     ~f:(fun acc q ->
                       let delta = Array.get nfa.transitions q in
                       let q' =
                         delta
                         |> List.filter (fun (label', _) -> Label.equal label label')
                         |> List.map snd
                       in
                       List.append q' acc)
                     ~init:[]
                     qs
                   |> Set.of_list
                 in
                 let q' =
                   if Set.equal qs' qs |> not
                   then (
                     visit qs';
                     Queue.add qs' queue;
                     q qs')
                   else q qs
                 in
                 (label, q') :: acc)
              []
              variations
          in
          let delta', final' = aux transitions final queue in
          delta :: delta', final')
        else aux transitions final queue)
    in
    let queue = Queue.create () in
    Queue.add nfa.start queue;
    let transitions, final = aux [] Set.empty queue in
    let transitions = Array.of_list transitions in
    { final; start = Set.singleton 0; transitions; deg = nfa.deg; is_dfa = true })
;;

let minimize nfa =
  nfa |> remove_unreachable |> to_dfa |> reverse |> to_dfa |> reverse |> to_dfa
;;

let invert nfa =
  (* We need complete DFA here, to_dfa() makes a complete DFA thus we're using it. *)
  let dfa = nfa |> to_dfa in
  let states = states dfa in
  let final = Set.diff states dfa.final in
  { final
  ; start = dfa.start
  ; transitions = dfa.transitions
  ; deg = dfa.deg
  ; is_dfa = true
  }
;;

let find_c_d (nfa : t) (imp : (int, int) Map.t) =
  assert (Set.length nfa.start = 1);
  let n = length nfa in
  let reachable_in_range = Graph.reachable_in_range nfa.transitions in
  let reachable_in n init = reachable_in_range n n init |> List.hd in
  let r1 =
    0 -- ((n * n) - 1) (* TODO: do not map, collect thing *)
    |> List.filter (fun i ->
      reachable_in i nfa.start |> Set.are_disjoint nfa.final |> not)
    |> Set.of_list
  in
  let states = reachable_in (n - 1) nfa.start in
  let states =
    states
    |> Set.to_sequence
    |> Sequence.filter_map ~f:(fun state ->
      Map.find imp state |> Option.map (fun d -> state, d))
  in
  let r2 =
    states
    |> Sequence.concat_map ~f:(fun (state, d) ->
      let first = (n * n) - n - d in
      let last = (n * n) - n - 1 in
      reachable_in_range first last (Set.singleton state)
      |> List.map (fun set -> not (Set.are_disjoint nfa.final set))
      |> Base.List.zip_exn (first -- last)
      |> List.filter snd
      |> List.map fst
      |> List.map (fun c -> c + n, d)
      |> Sequence.of_list)
    |> Sequence.map ~f:(fun (c, d) ->
      let rec helper c = if Set.mem r1 (c - d) then helper (c - d) else c in
      helper c, d)
    |> Sequence.to_list
  in
  let r1 =
    r1
    |> Set.to_list
    |> List.filter (fun c ->
      not (List.exists (fun (c1, d) -> c mod d = c1 mod d && c >= c1) r2))
    |> List.map (fun c -> c, 0)
  in
  r2 @ r1
;;

let get_exponent_sub_nfa (nfa : t) ~(res : deg) ~(temp : deg) : t =
  Debug.dump_nfa ~msg:"Exponent sub_nfa input: %s" format_nfa nfa;
  let mask = Bitv.init 32 (fun x -> x = res || x = temp) in
  let zero_lbl = Bitv.init 32 (Fun.const false), mask in
  let res_lbl = Bitv.init 32 (( = ) res), mask in
  let pow_lbl = Bitv.init 32 (( = ) temp), mask in
  let one_lbl = Bitv.init 32 (Fun.const true), mask in
  let reversed_transitions = nfa.transitions |> Graph.reverse in
  let end_transitions =
    reversed_transitions
    |> Array.mapi (fun src list ->
      if Set.mem nfa.final src
      then list |> List.filter (fun (lbl, _) -> Label.equal lbl res_lbl)
      else [])
  in
  let pre_final =
    end_transitions |> Array.to_list |> List.concat |> List.map snd |> Set.of_list
  in
  let zero_transitions, states =
    let all_zero_transitions =
      reversed_transitions
      |> Array.map (List.filter (fun (lbl, _) -> Label.equal lbl zero_lbl))
    in
    let rec helper acc visited cur =
      if Set.is_empty cur
      then acc, visited
      else (
        let next_transitions =
          all_zero_transitions
          |> Base.Array.mapi ~f:(fun i x -> if Set.mem cur i then x else [])
        in
        next_transitions |> Base.Array.iteri ~f:(fun i list -> acc.(i) <- list @ acc.(i));
        let visited = Set.union visited cur in
        let next =
          Set.diff
            (next_transitions
             |> Array.to_list
             |> List.concat_map (List.map snd)
             |> Set.of_list)
            visited
        in
        helper acc visited next)
    in
    helper (Array.map (Fun.const []) all_zero_transitions) Set.empty pre_final
  in
  let start =
    states
    |> Set.filter ~f:(fun i ->
      reversed_transitions.(i)
      |> List.filter (fun (lbl, _) -> Label.equal lbl pow_lbl)
      |> List.is_empty
      |> not)
  in
  let start_final =
    nfa.final
    |> Set.filter ~f:(fun i ->
      reversed_transitions.(i)
      |> List.filter (fun (lbl, _) -> Label.equal lbl one_lbl)
      |> List.is_empty
      |> not)
  in
  let start = Set.union start start_final in
  let transitions =
    Graph.union_list [ end_transitions; zero_transitions ] |> Graph.reverse
  in
  let result = { transitions; final = nfa.final; start; deg = nfa.deg; is_dfa = false } in
  Debug.dump_nfa ~msg:"Exponent sub_nfa output: %s" format_nfa result;
  result
;;

let chrobak (nfa : t) =
  Debug.dump_nfa ~msg:"Chrobak input: %s" format_nfa nfa;
  let important =
    Graph.find_important_verticies nfa.transitions
    |> List.filter (fun (_, b) -> b <> 0)
    |> Map.of_alist_exn
  in
  (* important *)
  (* |> Map.iteri ~f:(fun ~key ~data -> Format.printf "state=%d,d=%d\n" key data); *)
  let result = find_c_d nfa important in
  Debug.printf "Chrobak output:";
  Format.pp_print_list
    (fun fmt (a, b) -> Format.fprintf fmt " (%d, %d)" a b)
    Debug.fmt
    result;
  Debug.printfln "";
  result
;;

let get_chrobaks_sub_nfas nfa ~res ~temp ~vars =
  let mask = Bitv.init 32 (( = ) temp) in
  let temp_lbl = mask, mask in
  let exp_nfa = get_exponent_sub_nfa nfa ~res ~temp in
  exp_nfa.start
  |> Set.to_list
  |> List.filter_map (fun mid ->
    let* path = any_path { nfa with start = Set.singleton mid } vars in
    ( { nfa with
        final = Set.singleton mid
      ; transitions =
          nfa.transitions
          |> Array.map
               (List.filter (fun (lbl, fin) -> fin <> mid || Label.equal lbl temp_lbl))
      }
    , chrobak { exp_nfa with start = Set.singleton mid }
    , path )
    |> return)
;;
