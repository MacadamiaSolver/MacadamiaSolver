(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Angstrom

let ( << ) f g x = f (g x)

let is_whitespace = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

let whitespace = take_while is_whitespace

let is_digit = function '0' .. '9' -> true | _ -> false

let integer = take_while1 is_digit >>| (Ast.const << int_of_string)

let is_smallchar = function 'a' .. 'z' -> true | _ -> false

let varname =
  lift2
    (fun a b -> String.make 1 a ^ b)
    (satisfy is_smallchar) (take_while is_digit)

let var = varname >>| Ast.var

let sum = whitespace *> char '+' *> whitespace *> return Ast.add

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= go

let term =
  fix (fun _ ->
      let aterm = integer <|> var in
      chainl1 aterm sum )

let mand = whitespace *> char '&' *> whitespace *> return Ast.mand

let mor = whitespace *> char '|' *> whitespace *> return Ast.mor

let mimpl = whitespace *> string "->" *> whitespace *> return Ast.mimpl

let equals = whitespace *> char '=' *> whitespace *> return Ast.equals

let formula =
  fix (fun formula ->
      let equals =
        lift3
          (fun a _ b -> Ast.equals a b)
          term
          (whitespace *> char '=' *> whitespace)
          term
      in
      let mnot = char '~' *> whitespace *> formula >>| Ast.mnot in
      let exists =
        char 'E'
        *> lift2 (fun a b -> Ast.exists a b) varname (whitespace *> formula)
      in
      let any =
        char 'A'
        *> lift2 (fun a b -> Ast.any a b) varname (whitespace *> formula)
      in
      let aformula = parens formula <|> exists <|> any <|> mnot <|> equals in
      let aformula2 = chainl1 aformula mand in
      let aformula3 = chainl1 aformula2 mor in
      chainl1 aformula3 mimpl )

let parse (str : string) : Ast.formula =
  match parse_string ~consume:All formula str with
    | Ok v ->
        v
    | Error msg ->
        failwith msg
