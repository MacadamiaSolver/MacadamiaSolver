(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

module Map = Base.Map.Poly
module Nfa = Nfa.Lsb

type t =
  | Empty
  | Epsilon
  | Symbol of Bitv.t [@printer fun fmt -> fprintf fmt "%a" Bitv.L.print]
  | Mand of t * t
  | Mor of t * t
  | Concat of t * t
  | Kleene of t
  | Mnot of t
[@@deriving variants, show]

let all = mnot empty

let kleene = function
  | Kleene r -> kleene r
  | Epsilon -> Epsilon
  | Empty -> Epsilon
  | r -> kleene r
;;

let concat r' s' =
  match r', s' with
  | Empty, _ | _, Empty -> Empty
  | Epsilon, r | r, Epsilon -> r
  | r, s -> concat r s
;;

let mor r' s' =
  match r', s' with
  | Empty, r | r, Empty -> r
  | Mor (r, s), t when t = s || t = r -> mor r s
  | t, Mor (r, s) when t = s || t = r -> mor r s
  | Mnot Empty, _ | _, Mnot Empty -> all
  | r, s when r = s -> r
  | r, s -> mor r s
;;

let mand r' s' =
  match r', s' with
  | Empty, _ | _, Empty -> Empty
  | Epsilon, _ | _, Epsilon -> Epsilon
  | Mnot Empty, r | r, Mnot Empty -> r
  | Mand (r, s), t when t = s || t = r -> mand r s
  | t, Mand (r, s) when t = s || t = r -> mand r s
  | r, s when r = s -> r
  | r, s -> mand r s
;;

let mnot = function
  | Mnot (Mnot r) -> r
  | r -> mnot r
;;

let ( <|> ) = mor
let ( <&> ) = mand
let ( <*> ) = concat

let rec v = function
  | Empty -> false
  | Epsilon -> true
  | Symbol _ -> false
  | Concat (r, s) -> v r && v s
  | Mor (r, s) -> v r || v s
  | Mand (r, s) -> v r && v s
  | Kleene _ -> true
  | Mnot r -> v r |> not
;;

let rec deriv a = function
  | Empty -> Empty
  | Epsilon -> Empty
  | Symbol b -> if Bitv.equal a b then Epsilon else Empty
  | Concat (r, s) -> if v r then deriv a r <*> s <|> deriv a s else deriv a r <*> s
  | Mor (r, s) -> deriv a r <|> deriv a s
  | Mand (r, s) -> deriv a r <&> deriv a s
  | Kleene r -> deriv a r <*> kleene r
  | Mnot r -> mnot (deriv a r)
;;

let rec symbols = function
  | Empty | Epsilon -> []
  | Symbol a -> [ a ]
  | Concat (r, s) | Mor (r, s) | Mand (r, s) -> List.append (symbols r) (symbols s)
  | Kleene r | Mnot r -> symbols r
;;

let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []
;;

let to_nfa r =
  let rec traverse visited = function
    | [] -> []
    | r :: tl ->
      if List.exists (fun r' -> r' = r) visited
      then traverse visited tl
      else (
        let visited = r :: visited in
        let symbols = symbols r in
        let delta = List.map (fun symbol -> symbol, deriv symbol r) symbols in
        let tl = List.append (List.map snd delta) tl in
        (r, delta) :: traverse visited tl)
  in
  let transitions = traverse [] [ r ] in
  let regex_to_state =
    transitions |> List.map fst |> List.mapi (fun i r -> r, i) |> Map.of_alist_exn
  in
  let finals = Map.keys regex_to_state |> List.filter v in
  let regex_to_state = Map.find_exn regex_to_state in
  let transitions =
    transitions
    |> List.concat_map (fun (q, delta) ->
      List.map
        (fun (l, q') -> regex_to_state q, l |> Bitv.to_int_us, regex_to_state q')
        delta)
  in
  let deg = symbols r |> List.fold_left (fun acc v -> max acc (Bitv.length v)) 0 in
  Nfa.create_nfa
    ~transitions
    ~start:[ regex_to_state r ]
    ~final:(finals |> List.map regex_to_state)
    ~vars:(0 -- (deg - 1) |> List.rev)
    ~deg
;;

open Angstrom

let of_string =
  let is_whitespace = function
    | ' ' | '\t' | '\n' | '\r' -> true
    | _ -> false
  in
  let whitespace = take_while is_whitespace in
  let token t = whitespace *> t <* whitespace in
  let parens t = token (char '(') *> t <* token (char ')') in
  let symbol =
    let* str =
      token (char '[') *> many (token (char '0' <|> char '1') <* whitespace)
      <* token (char ']')
    in
    str |> List.to_seq |> String.of_seq |> Bitv.L.of_string |> symbol |> return
  in
  let un_op f op s = token (string op) *> s >>| f <|> s in
  let bin_op f op =
    let op = token (string op) *> return f in
    let chainl1 op e =
      let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
      e >>= go
    in
    chainl1 op
  in
  let regex =
    fix (fun regex ->
      parens regex
      <|> symbol
      |> un_op kleene "*"
      |> bin_op concat "/"
      |> bin_op mand "&"
      |> bin_op mor "|")
  in
  parse_string ~consume:Prefix regex
;;

let%expect_test "Basic parsing" =
  of_string "[01]/*([10]|[11]/[01])" |> Result.get_ok |> Format.printf "%a@." pp;
  [%expect
    {| (Regex.Concat (01, (Regex.Kleene (Regex.Mor (10, (Regex.Concat (11, 01))))))) |}]
;;

let%expect_test "Basic derivatives" =
  of_string "[01]/[10]"
  |> Result.get_ok
  |> deriv (Bitv.L.of_string "01")
  |> Format.printf "%a@.\n" pp;
  of_string "[0]/*[1]"
  |> Result.get_ok
  |> deriv (Bitv.L.of_string "0")
  |> Format.printf "%a@.\n" pp;
  (of_string "[00]/[10]|[00]/[01]"
   |> Result.get_ok
   |> deriv (Bitv.L.of_string "00")
   |> (fun x ->
   Format.printf "%a@." pp x;
   x)
   |> deriv (Bitv.L.of_string "00")
   |> (fun x ->
   Format.printf "%a@." pp x;
   x)
   |> deriv (Bitv.L.of_string "01")
   |> fun x -> Format.printf "%a@.\n" pp x);
  (of_string "[00]/[10]|[00]/[01]"
   |> Result.get_ok
   |> deriv (Bitv.L.of_string "00")
   |> (fun x ->
   Format.printf "%a@." pp x;
   x)
   |> deriv (Bitv.L.of_string "10")
   |> fun x -> Format.printf "%a@.\n" pp x);
  [%expect
    {|
    10

    (Regex.Kleene 1)

    (Regex.Mor (10, 01))
    Regex.Empty
    Regex.Empty

    (Regex.Mor (10, 01))
    Regex.Epsilon
    |}]
;;

let%expect_test "To nfa basic" =
  of_string "[00]/[10]|[00]/[01]"
  |> Result.get_ok
  |> to_nfa
  |> Format.printf "%a@." Nfa.format_nfa;
  [%expect
    {|
    digraph {
    node [shape=circle]
    "2" [shape=doublecircle]
    "0" [shape=octagon]
    "0" -> "1" [label="(00)
    (00)"]
    "0" -> "3" [label="(01)
    (10)"]
    "1" -> "2" [label="(01)
    (10)"]
    }
    |}]
;;

let%expect_test "To nfa and predicate" =
  of_string "*([000]|[100]|[010]|[111])"
  |> Result.get_ok
  |> to_nfa
  |> Format.printf "%a@." Nfa.format_nfa;
  [%expect
    {|
    digraph {
    node [shape=circle]
    "0" [shape=doubleoctagon]
    "0" -> "0" [label="(111)
    (010)
    (100)
    (000)"]
    }
    |}]
;;
