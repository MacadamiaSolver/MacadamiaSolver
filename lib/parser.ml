(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Angstrom

let ( << ) f g x = f (g x)

let is_whitespace = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

let whitespace = take_while is_whitespace

let is_digit = function '0' .. '9' -> true | _ -> false

let const = take_while1 is_digit >>| (Ast.const << int_of_string)

let is_idchar = function 'a' .. 'z' | '_' | '0' .. '9' -> true | _ -> false

let varname = take_while1 is_idchar
let var = varname >>| Ast.var

let integer = take_while1 is_digit >>| int_of_string

let mul term =
  lift3
    (fun a _ b -> Ast.mul a b)
    (integer <* whitespace) (char '*') (whitespace *> term)

let sum = whitespace *> char '+' *> whitespace *> return Ast.add

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= go

let term =
  fix (fun term ->
      let aterm1 = parens term <|> const <|> var in
      let aterm2 = mul aterm1 <|> aterm1 in
      chainl1 aterm2 sum )

let mand = whitespace *> char '&' *> whitespace *> return Ast.mand

let mor = whitespace *> char '|' *> whitespace *> return Ast.mor

let mimpl = whitespace *> string "->" *> whitespace *> return Ast.mimpl

let pred_params =
  fix (fun pred_params ->
      lift2 (fun a b -> List.cons a b) (whitespace *> term) pred_params
      <|> return [] )

let predname = take_while1 is_idchar

let pred =
  lift2
    (fun a b -> Ast.pred a b)
    (predname <* whitespace)
    (char '(' *> pred_params <* whitespace <* char ')')

let equals =
  lift3
    (fun a _ b -> Ast.equals a b)
    term
    (whitespace *> char '=' *> whitespace)
    term

let mnot aformula = char '~' *> whitespace *> aformula >>| Ast.mnot

let exists formula =
  char 'E' *> lift2 (fun a b -> Ast.exists a b) varname (whitespace *> formula)

let any formula = char 'A' *> lift2 (fun a b -> Ast.any a b) varname (whitespace *> formula)

let formula =
  fix (fun formula ->
      let aformula = parens formula <|> equals <|> pred in
      let aformula1 = mnot formula <|> aformula in
      let aformula2 = chainl1 aformula1 mand in
      let aformula3 = chainl1 aformula2 mor in
      let aformula4 = chainl1 aformula3 mimpl in
      exists formula <|> any formula <|> aformula4)

let eval = string "eval" *> whitespace *> formula >>| Ast.eval

let dump = string "dump" *> whitespace *> formula >>| Ast.dump

let def_params =
  fix (fun def_params ->
      lift2 (fun a b -> List.cons a b) (whitespace *> varname) def_params
      <|> return [] )

let def =
  lift3
    (fun n p f -> Ast.def n p f)
    (string "let" *> whitespace *> predname)
    def_params
    (whitespace *> char '=' *> whitespace *> formula)

let stmt = eval <|> def <|> dump <|> fail "Unknown statement kind"

let parse_formula str = parse_string ~consume:All formula str

let parse str = parse_string ~consume:All stmt str
