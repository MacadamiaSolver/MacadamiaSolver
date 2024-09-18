(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib
module Map = Nfa.Map

open Format

type atom =
  | Var of string
  | Const of int
  | Internal of int

let format_atom ppf = function
  | Var a -> fprintf ppf "Var %s" a
  | Const a -> fprintf ppf "Const %d" a
  | Internal a -> fprintf ppf "Internal %d" a

let nfa_unit = NfaCollection.Neutral.n () |> Nfa.to_nfa

let rec teval = function
  | Ast.Var a -> (Var a, nfa_unit)
  | Ast.Const a -> (Const a, nfa_unit)
  | Ast.Add (l, r) ->
    let (lv, la) = teval l in
    let (rv, ra) = teval r in
    let res = Internal (Oo.id object end) in
    (res,
    NfaCollection.Add.add ~lhs:lv ~rhs:rv ~sum:res
    |> Nfa.to_nfa
    |> Nfa.intersect la
    |> Nfa.intersect ra
    |> Nfa.remove_unreachable)
  | Ast.Mul (a, b) ->
    let rec teval_mul a b =
      match a with
      | 0 -> (Const 0, nfa_unit)
      | 1 -> teval b
      | _ ->
        match a mod 2 with
          | 0 -> 
            let (tv, ta) = teval_mul (a / 2) b in
            let res = Internal (Oo.id object end) in
            (res,
            NfaCollection.Add.add ~lhs:tv ~rhs:tv ~sum:res
            |> Nfa.to_nfa
            |> Nfa.intersect ta
            |> Nfa.remove_unreachable)
          | 1 ->
            let (tv, ta) = teval_mul (a - 1) b in
            let (uv, ua) = teval b in
            let res = Internal (Oo.id object end) in
            (res,
            NfaCollection.Add.add ~lhs:tv ~rhs:uv ~sum:res
            |> Nfa.to_nfa
            |> Nfa.intersect ta
            |> Nfa.intersect ua
            |> Nfa.remove_unreachable)
          | _ -> assert false
      in
    teval_mul a b

let rec eval state = function
  | Ast.Equals (l, r) ->
    let (lv, la) = teval l in
    let (rv, ra) = teval r in
    NfaCollection.Eq.eq lv rv
    |> Nfa.to_nfa
    |> Nfa.intersect la
    |> Nfa.intersect ra
    |> Nfa.project (function
      | Var _
      | Const _ -> true
      | Internal _ -> false)
    |> Nfa.remove_unreachable
    |> Result.ok
  | Ast.Mnot f -> Result.error "Not is not yet implemented"
  | Ast.Mand (f1, f2) ->
    let lr = eval state f1 in
    let rr = eval state f2 in
    (match (lr, rr) with
      | (Ok la, Ok ra) -> Nfa.intersect la ra |> Result.ok
      | (Error _, _) -> lr
      | _ -> rr)
  | Ast.Mor (f1, f2) ->
    Result.error "Or is not yet implemented"
  | Ast.Exists (x, f) ->
    let a = eval state f in
    (match a with
      | Ok a ->
        Nfa.project ((<>) (Var x)) a
        |> Nfa.remove_unreachable
        |> Result.ok
      | _ -> a)
  | Ast.Pred (name, args) ->
    let args = List.map teval args in
    (match List.find_opt (fun (pred_name, _, _) -> pred_name = name) state with
      | Some (_, pred_params, pred_nfa) ->
        pred_nfa
        |> Nfa.map_varname
          (function
            | Var s ->
              (match List.find_index ((=) s) pred_params with
                | Some i ->
                  (match List.nth_opt args i with
                    | Some (av, _) -> av
                    | None -> Var s)
                | None -> Var s)
            | x -> x)
        |> List.fold_right
          (fun acc a -> Nfa.intersect acc a)
          (List.map (fun (av, aa) -> aa) args)
        |> Result.ok
      | None -> Printf.sprintf "Unknown predicate %s" name |> Result.error)
  | _ -> Result.error "unimplemented"

let exec state = function
  | Ast.Eval f ->
    let res = eval state f in
    (match res with
    | Ok nfa ->
      let res = Nfa.run_nfa
        nfa
          ((List.init 63 (fun x -> x + 1))
          |> List.map (fun i ->
              (Map.singleton (Const 1) (List.nth (Bits.to_bit_string 1) (i - 1))))) in
      Format.printf "Result: %b\n\n" res; state
    | Error msg -> Format.printf "Error: %s\n\n" msg; state)
  | Ast.Dump f ->
    let res = eval state f in
    (match res with
    | Ok nfa ->
      Format.printf "%a\n\n" (Nfa.format_nfa format_atom) nfa; state
    | Error msg -> Format.printf "Error: %s\n\n" msg; state)
  | Ast.Def (name, params, formula) ->
    match eval state formula with
    | Ok nfa -> 
      (name, params, nfa) :: state
    | Error msg -> Format.printf "Error: %s\n\n" msg; state

let () =
  let rec input_and_solve state =
    let line = read_line () in
    let stmt = Parser.parse line in
    match stmt with
    | Ok stmt ->
      (*match exec stmt with
      | Ok state -> input_and_solve state
      | Error msg -> Format.printf "Error: %s\n\n" msg;*)
      exec state stmt |> input_and_solve ;
    | Error msg ->
      Format.printf "Error: %s\n\n" msg;
      input_and_solve state;
  in
  input_and_solve []

      (*Format.printf "Result: %B\n\n" res*)
