(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

open Lib
module Map = Base.Map.Poly

let help () =
  Format.printf
    {|
Chrobelias REPL help.

This is an utility tool for proving some of the theorems and debugging the
algorithms. If you want to execute an .smt2 file use smtlib tool.

Commands

* let <name> <arg1> ... [argN] = <formula> - define a predicate.
* letr <name> = <regex>                    - define a regular predicate.
* eval <formula>                           - proof a PrA theorem.
* evalm <formula>                          - get model for PrA formula.
* dump <formula>                           - draw NFA for the formula
                                             (needs xdg-open).
* list                                     - list regular predicates.
* help                                     - see help

Prove Frobenius coin problem using the solver in PrA:

    > eval AxEyEz x = 3*y + 5*z | x <= 7

Or check out existential Semenov arithmetic allowing 2**x as a functional
symbol:

    > eval Ex 2**x = x + 3

You might define your own predicates as follows:

    > let even x = Ey x = 2*y

    > eval even 2
      sat
    > eval even 3
      unsat

Or bitwise-regular predicates as follows:

    > letr land = *([000]|[010]|[100]|[111])
    > letr lone = [1]/*[0]

    > eval land 6 3 2
      sat
    > eval lone 2
      unsat

|}
;;

let exec line = function
  | Ast.Eval f ->
    let res = Solver.proof f in
    (match res with
     | Ok res -> if res then Format.printf "sat\n\n%!" else Format.printf "unsat\n\n%!"
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.Evalm f ->
    let res = Solver.get_model f in
    (match res with
     | Ok res ->
       (match res with
        | Some model ->
          Map.iteri ~f:(fun ~key:k ~data:v -> Format.printf "%s = %d; " k v) model;
          Format.printf "\n%!"
        | None -> Format.printf "no model\n\n%!")
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
  | Ast.Defr (name, regex) ->
    (match Solver.predr name regex with
     | Ok () -> ()
     | Error msg -> Format.printf "Error: %s\n\n%!" msg)
  | Ast.Parse f ->
    Format.printf "Formula AST: %a\n%!" Ast.pp_formula f;
    Format.printf "Optimized AST: %a\n\n%!" Ast.pp_formula (f |> Optimizer.optimize)
  | Ast.List -> Solver.list ()
  | Ast.Help -> help ()
;;

let welcome () =
  Format.printf
    {|Welcome to Chrobelias REPL. Use `help` to see available commands.

|}
;;

let () =
  welcome ();
  let rec aux () =
    try
      Format.printf "> %!";
      let line = read_line () in
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
