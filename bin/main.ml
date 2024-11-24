(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Lib

let () =
  let rec input_and_solve () =
    let expr = read_line () in
    let ast = Parser.parse_formula expr in
    match ast with
      | Ok f ->
          input_and_solve (Format.printf "%a" Ast.pp_formula f)
      | Error err ->
          input_and_solve (Format.printf "Error: %s" err)
  in
  input_and_solve ()
