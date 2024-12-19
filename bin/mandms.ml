(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib

let exec line = function
  | Ast.Eval f ->
    let res = Solver.proof f in
    (match res with
     | Ok res -> Format.printf "Result: %b\n\n%!" res
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.EvalSemenov f ->
    let res = Solver.proof_semenov f in
    (match res with
     | Ok res -> Format.printf "Result: %b\n\n%!" res
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.Dump f ->
    (match Solver.dump f with
     | Ok s ->
       let dot_file = Format.sprintf "dumps/\"%s.dot\"" line in
       let svg_file = Format.sprintf "dumps/\"%s.svg\"" line in
       let oc = open_out (Format.sprintf "dumps/%s.dot" line) in
       let command =
         Format.sprintf
           "mkdir -p dumps/; dot -Tsvg %s > %s; xdg-open %s"
           dot_file
           svg_file
           svg_file
       in
       Printf.fprintf oc "%s" s;
       close_out oc;
       Sys.command command |> ignore
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.Def (name, params, formula) ->
    (match Solver.pred name params formula with
     | Ok () -> ()
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.Parse f ->
    Format.printf "Formula AST: %a\n%!" Ast.pp_formula f;
    Format.printf "Optimized AST: %a\n\n%!" Ast.pp_formula (f |> Optimizer.optimize)
  | Ast.List -> Solver.list ()
  | Ast.Help -> ()
;;

let () =
  let rec aux () =
    try
      Format.printf "> %!";
      let line = read_line () in
      Format.printf "  %!";
      let stmt = Parser.parse line in
      (match stmt with
       | Ok stmt -> exec line stmt
       | Error msg -> Format.printf "Error: %s\n\n%!" msg);
      aux ()
    with
    | End_of_file -> ()
  in
  aux ()
;;
