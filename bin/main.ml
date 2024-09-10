(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib

let () =
  let rec input_and_solve () =
    let expr = read_line () in
    let ast = Parser.parse expr in
    input_and_solve (print_endline (Ast.string_of_formula ast))
  in
  input_and_solve ()
