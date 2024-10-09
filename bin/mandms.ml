(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib
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

let state = ref []
let cur = ref 0
let acur = ref 0

let rec testimate t = match t with
  | Ast.Const _
  | Ast.Var _ -> 1
  | Ast.Add (t1, t2) -> 1 + testimate t1 + testimate t2
  | Ast.Mul (_, t1) -> 1 + testimate t1

let rec estimate f = match f with
  | Ast.Eq (t1, t2)
  | Ast.Lt (t1, t2)
  | Ast.Gt (t1, t2)
  | Ast.Leq (t1, t2)
  | Ast.Geq (t1, t2)
  | Ast.Neq (t1, t2) -> 1 + testimate t1 + testimate t2
  | Ast.Mor (f1, f2)
  | Ast.Mand (f1, f2)
  | Ast.Mimpl (f1, f2) -> 1 + estimate f1 + estimate f2
  | Ast.Mnot f1 -> 1 + estimate f1
  | Ast.Exists (_, f1)
  | Ast.Any (_, f1) -> 1 + estimate f1
  | Ast.Pred (_, args) -> 1 + List.fold_left (fun acc x -> acc + testimate x) 0 args
  | _ -> 1

let progress () =
  let pl = 12 in
  let rec repeat n s =
    if n <= 0 then "" else s ^ repeat (n - 1) s in
  let c = ((Float.of_int !cur) /. (Float.of_int !acur) *. Float.of_int(pl)) |> Int.of_float in
  Printf.printf "%s" (repeat 80 "\b");
  Printf.printf "[%s%s] [%0#3d/%0#3d]%!" (repeat c "\u{2588}") (repeat (pl - c) " ") !cur !acur

let rec teval ast = 
  let nfa_unit = NfaCollection.Neutral.n () |> Nfa.to_nfa in

  let nfa = match ast with
  | Ast.Var a ->
      (Var a, nfa_unit)
  | Ast.Const a ->
      let res = Internal (Oo.id (object end)) in
      (res, NfaCollection.Eq.eq_const res a |> Nfa.to_nfa)
  | Ast.Add (l, r) ->
      let lv, la = teval l in
      let rv, ra = teval r in
      let res = Internal (Oo.id (object end)) in
      ( res
      , NfaCollection.Add.add ~lhs:lv ~rhs:rv ~sum:res
        |> Nfa.to_nfa |> Nfa.intersect la |> Nfa.intersect ra
        |> Nfa.remove_unreachable )
  | Ast.Mul (a, b) ->
      let rec teval_mul a b =
        match a with
          | 0 ->
              let res = Internal (Oo.id (object end)) in
              (res, NfaCollection.Eq.eq_const res 0 |> Nfa.to_nfa)
          | 1 ->
              teval b
          | _ -> (
            match a mod 2 with
              | 0 ->
                  let tv, ta = teval_mul (a / 2) b in
                  let res = Internal (Oo.id (object end)) in
                  ( res
                  , NfaCollection.Add.add ~lhs:tv ~rhs:tv ~sum:res
                    |> Nfa.to_nfa |> Nfa.intersect ta |> Nfa.remove_unreachable
                  )
              | 1 ->
                  let tv, ta = teval_mul (a - 1) b in
                  let uv, ua = teval b in
                  let res = Internal (Oo.id (object end)) in
                  ( res
                  , NfaCollection.Add.add ~lhs:tv ~rhs:uv ~sum:res
                    |> Nfa.to_nfa |> Nfa.intersect ta |> Nfa.intersect ua
                    |> Nfa.remove_unreachable )
              | _ ->
                  assert false )
      in teval_mul a b in
  cur := (!cur) + 1;
  progress ();
  nfa

let eval ast = 
  let rec eval ast =
    let nfa = match ast with
    | Ast.Eq (l, r) ->
        let lv, la = teval l in
        let rv, ra = teval r in
        NfaCollection.Eq.eq lv rv |> Nfa.to_nfa |> Nfa.intersect la
        |> Nfa.intersect ra
        |> Nfa.project (function Var _ | Const _ -> true | Internal _ -> false)
        |> Nfa.remove_unreachable |> Result.ok
    | Ast.Mnot f -> (
      match eval f with
        | Ok v ->
            Nfa.to_dfa v |> Nfa.minimize |> Nfa.invert |> Nfa.to_nfa
            |> Nfa.remove_unreachable |> Result.ok
        | _ as a ->
            a )
    | Ast.Mand (f1, f2) -> (
        let lr = eval f1 in
        let rr = eval f2 in
        match (lr, rr) with
          | Ok la, Ok ra ->
              Nfa.intersect la ra |> Result.ok
          | Error _, _ ->
              lr
          | _ ->
              rr )
    | Ast.Mor (f1, f2) -> (
        let lr = eval f1 in
        let rr = eval f2 in
        match (lr, rr) with
          | Ok la, Ok ra ->
              Nfa.unite la ra |> Result.ok
          | Error _, _ ->
              lr
          | _ ->
              rr )
    | Ast.Mimpl (f1, f2) -> (
          let lr = eval f1 in
          let rr = eval f2 in
          match (lr, rr) with
            | Ok la, Ok ra ->
                Nfa.unite (la |> Nfa.to_dfa |> Nfa.minimize |> Nfa.invert |> Nfa.to_nfa) ra |> Result.ok
            | Error _, _ ->
                lr
            | _ ->
                rr )
    | Ast.Exists (x, f) -> (
      match eval f with
        | Ok a ->
            Nfa.project (( <> ) (Var x)) a
            |> Nfa.to_dfa |> Nfa.minimize |> Nfa.to_nfa |> Result.ok
        | _ as a ->
            a )
    | Ast.Any (x, f) -> (
      match eval f with
        | Ok v ->
            Nfa.to_dfa v |> Nfa.minimize |> Nfa.invert |> Nfa.to_nfa
            |> Nfa.remove_unreachable
            |> Nfa.project (( <> ) (Var x))
            |> Nfa.to_dfa |> Nfa.minimize |> Nfa.invert |> Nfa.to_nfa
            |> Nfa.remove_unreachable |> Result.ok
        | _ as a ->
            a )
    | Ast.Pred (name, args) -> (
        let args = List.map teval args in
        match List.find_opt (fun (pred_name, _, _, _) -> pred_name = name) !state with
          | Some (_, pred_params, _, pred_nfa) ->
              let nfa =
                pred_nfa
                |> Nfa.map_varname (function
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
                     (fun acc a -> Nfa.intersect acc a)
                     (List.map (fun (_, arg) -> arg) args)
                |> Nfa.project (function
                     | Var _ | Const _ ->
                         true
                     | Internal _ ->
                         false )
              in
              Result.ok nfa
          | None ->
              Printf.sprintf "Unknown predicate %s" name |> Result.error )
    | _ -> failwith "unimplemented" in
    cur := (!cur) + 1;
    progress ();
    nfa
  in
  cur := 0;
  acur := estimate ast;
  let res = eval ast in
  Format.printf "\n%!";
  res


let list state =
  let rec aux = function
  | [] -> ()
  | (name, params, formula, _) :: xs -> Format.printf "%s %a = %a\n%!" name (Format.pp_print_list Format.pp_print_string) params Ast.pp_formula formula; aux xs in
  aux state

let exec line = function
  | Ast.Eval f -> (
      let res = eval f in
      match res with
        | Ok nfa ->
            let res = Nfa.run_nfa nfa [] in
            Format.printf "Result: %b\n\n%!" res;
        | Error msg ->
            Format.printf "Error: %s\n\n%!" msg;)
  | Ast.Dump f -> (
      let res = eval f in
      match res with
        | Ok nfa ->
            let dot_file = Format.sprintf "dumps/\"%s.dot\"" line in
            let svg_file = Format.sprintf "dumps/\"%s.svg\"" line in
            let oc = open_out (Format.sprintf "dumps/%s.dot" line) in
            let out = Format.asprintf "%a" (Nfa.format_nfa format_atom) nfa in
            let command =
              Format.sprintf "mkdir -p dumps/; dot -Tsvg %s > %s; xdg-open %s"
                dot_file svg_file svg_file
            in
            Printf.fprintf oc "%s" out;
            close_out oc;
            Sys.command command |> ignore;
        | Error msg ->
            Format.printf "Error: %s\n\n%!" msg;)
  | Ast.Def (name, params, formula) -> (
    match eval formula with
      | Ok nfa ->
        state := (name, params, formula, nfa) :: !state
      | Error msg ->
          Format.printf "Error: %s\n\n%!" msg;)
  | Ast.Parse f ->
      Format.printf "Formula AST: %a\n\n%!" Ast.pp_formula f;
  | Ast.List ->
      list !state;
  | Ast.Help -> ()


let () =
  let rec aux () =
    let line = read_line () in
    let stmt = Parser.parse line in
    match stmt with
      | Ok stmt ->
          exec line stmt;
          aux ()
      | Error msg ->
          Format.printf "Error: %s\n\n%!" msg;
          aux ()
    in
  aux ()
