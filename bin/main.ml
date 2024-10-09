(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib
module Map = Dfa.Map
module Set = Base.Set.Poly
open Format

type atom = Var of string | Const of int | Internal of int

let _ = Const 1

let format_atom ppf = function
  | Var a ->
      fprintf ppf "Var %s" a
  | Const a ->
      fprintf ppf "Const %d" a
  | Internal a ->
      fprintf ppf "Internal %d" a

(* let dbg x = *)
(*   x |> Format.printf "Debug: %a\n" (Dfa.format format_atom); *)
(*   x *)

let rec teval = function
  | Ast.Var a ->
      (Var a, DfaCollection.any ())
  | Ast.Const a ->
      let res = Internal (Oo.id (object end)) in
      (res, DfaCollection.eq_const res a)
  | Ast.Add (l, r) ->
      let lv, la = teval l in
      let rv, ra = teval r in
      let res = Internal (Oo.id (object end)) in
      ( res
      , DfaCollection.add ~lhs:lv ~rhs:rv ~sum:res
        |> Dfa.intersect la |> Dfa.intersect ra
        |> Dfa.project (function Var _ | Const _ -> true | t -> t = res) )
  | Ast.Mul (a, b) ->
      let rec teval_mul a b =
        match a with
          | 0 ->
              let res = Internal (Oo.id (object end)) in
              (res, DfaCollection.eq_const res 0)
          | 1 ->
              teval b
          | _ -> (
            match a mod 2 with
              | 0 ->
                  let tv, ta = teval_mul (a / 2) b in
                  let res = Internal (Oo.id (object end)) in
                  ( res
                  , DfaCollection.add ~lhs:tv ~rhs:tv ~sum:res
                    |> Dfa.intersect ta
                    |> Dfa.project (function
                         | Var _ | Const _ ->
                             true
                         | t ->
                             t = res ) )
              | 1 ->
                  let tv, ta = teval_mul (a - 1) b in
                  let uv, ua = teval b in
                  let res = Internal (Oo.id (object end)) in
                  ( res
                  , DfaCollection.add ~lhs:tv ~rhs:uv ~sum:res
                    |> Dfa.intersect ta |> Dfa.intersect ua
                    |> Dfa.project (function
                         | Var _ | Const _ ->
                             true
                         | t ->
                             t = res ) )
              | _ ->
                  assert false )
      in
      teval_mul a b

let rec eval state = function
  | Ast.Equals (l, r) ->
      let lv, la = teval l in
      let rv, ra = teval r in
      DfaCollection.eq lv rv |> Dfa.intersect la |> Dfa.intersect ra
      |> Dfa.project (function Var _ | Const _ -> true | Internal _ -> false)
      |> Result.ok
  | Ast.Mnot f -> (
    match eval state f with
      | Ok v ->
          v |> Dfa.minimize |> Dfa.invert |> Dfa.remove_unreachable |> Result.ok
      | _ as a ->
          a )
  | Ast.Mand (f1, f2) -> (
      let lr = eval state f1 in
      let rr = eval state f2 in
      match (lr, rr) with
        | Ok la, Ok ra ->
            Dfa.intersect la ra |> Result.ok
        | Error _, _ ->
            lr
        | _ ->
            rr )
  | Ast.Mor (f1, f2) -> (
      let lr = eval state f1 in
      let rr = eval state f2 in
      match (lr, rr) with
        | Ok la, Ok ra ->
            Dfa.union la ra |> Result.ok
        | Error _, _ ->
            lr
        | _ ->
            rr )
  | Ast.Mimpl (f1, f2) -> (
      let lr = eval state f1 in
      let rr = eval state f2 in
      match (lr, rr) with
        | Ok la, Ok ra ->
            Dfa.union (Dfa.invert la) ra |> Result.ok
        | Error _, _ ->
            lr
        | _ ->
            rr )
  | Ast.Exists (x, f) -> (
    match eval state f with
      | Ok a ->
          a |> Dfa.project (( <> ) (Var x)) |> Result.ok
      | _ as a ->
          a )
  | Ast.Any (x, f) -> (
    match eval state f with
      | Ok v ->
          v |> Dfa.minimize |> Dfa.invert |> Dfa.remove_unreachable
          |> Dfa.project (( <> ) (Var x))
          |> Dfa.invert |> Dfa.remove_unreachable |> Result.ok
      | _ as a ->
          a )
  | Ast.Pred (name, args) -> (
      let args = List.map teval args in
      match List.find_opt (fun (pred_name, _, _) -> pred_name = name) state with
        | Some (_, pred_params, pred_nfa) ->
            let nfa =
              pred_nfa
              |> Dfa.map_varname (function
                   | Var s -> (
                     match List.find_index (( = ) s) pred_params with
                       | Some i -> (
                         match List.nth_opt args i with
                           | Some (av, _) ->
                               av
                           | None ->
                               Var s )
                       | None ->
                           Var s )
                   | x ->
                       x )
              |> List.fold_right
                   (fun acc a -> Dfa.intersect acc a)
                   (List.map (fun (_, arg) -> arg) args)
              |> Dfa.project (function
                   | Var _ | Const _ ->
                       true
                   | Internal _ ->
                       false )
            in
            Result.ok nfa
        | None ->
            Printf.sprintf "Unknown predicate %s" name |> Result.error )

let exec state line = function
  | Ast.Eval f -> (
      let res = eval state f in
      match res with
        | Ok dfa ->
            let res = Dfa.run dfa [] in
            Format.printf "Result: %b\n\n" res;
            state
        | Error msg ->
            Format.printf "Error: %s\n\n" msg;
            state )
  | Ast.Dump f -> (
      let res = eval state f in
      match res with
        | Ok nfa ->
            let dot_file = Format.sprintf "dumps/\"%s.dot\"" line in
            let svg_file = Format.sprintf "dumps/\"%s.svg\"" line in
            let oc = open_out (Format.sprintf "dumps/%s.dot" line) in
            let out = Format.asprintf "%a" (Dfa.format format_atom) nfa in
            let command =
              Format.sprintf "mkdir -p dumps/; dot -Tsvg %s > %s; xdg-open %s"
                dot_file svg_file svg_file
            in
            Printf.fprintf oc "%s" out;
            close_out oc;
            Sys.command command |> ignore;
            state
        | Error msg ->
            Format.printf "Error: %s\n\n" msg;
            state )
  | Ast.Def (name, params, formula) -> (
    match eval state formula with
      | Ok nfa ->
          (name, params, nfa) :: state
      | Error msg ->
          Format.printf "Error: %s\n\n" msg;
          state )

let () =
  let rec input_and_solve state =
    let line = read_line () in
    let stmt = Parser.parse line in
    match stmt with
      | Ok stmt ->
          (*match exec stmt with
            | Ok state -> input_and_solve state
            | Error msg -> Format.printf "Error: %s\n\n" msg;*)
          exec state line stmt |> input_and_solve
      | Error msg ->
          Format.printf "Error: %s\n\n" msg;
          input_and_solve state
  in
  (*Format.printf "Result: %d\n\n" (match List.nth (Bits.to_bit_string 2) (2 - 1) with
    | Bits.I -> 1
    | Bits.O -> 0);*)
  input_and_solve []
