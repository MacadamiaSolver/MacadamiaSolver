(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Angstrom

let is_whitespace = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

let whitespace = take_while is_whitespace

let is_digit = function '0' .. '9' -> true | _ -> false

let const = take_while1 is_digit >>| int_of_string >>| Ast.const

let is_idschar = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false

let is_idchar = function
  | 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' ->
      true
  | _ ->
      false

let ident =
  let* a = satisfy is_idschar in
  let* b = take_while is_idchar in
  String.make 1 a ^ b |> return

let var = ident >>| Ast.var

let integer = take_while1 is_digit >>| int_of_string

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= go

let un_op op ast p = string op *> whitespace *> p >>| ast

let bin_op op ast p =
  let op = whitespace *> string op *> whitespace *> return ast in
  chainl1 p op

let opt q p = q p <|> p

let mul term =
  let* c = integer <* whitespace in
  let* body = term in
  Ast.mul c body |> return

let term =
  fix (fun term ->
      parens term <|> const <|> var |> opt mul |> bin_op "+" Ast.add )

let pred =
  let* name = take_while1 is_idchar <* whitespace in
  let* params = whitespace *> term |> many <* whitespace in
  Ast.pred name params |> return

let pred_op op ast =
  let* a = term in
  let* _ = whitespace *> string op <* whitespace in
  let* b = term in
  ast a b |> return

let aformula =
  pred_op "=" Ast.eq <|> pred_op "!=" Ast.neq <|> pred_op "<" Ast.lt
  <|> pred_op ">" Ast.gt <|> pred_op "<=" Ast.geq <|> pred_op ">=" Ast.leq
  <|> pred

let quantifier sym ast formula =
  let* _ = char sym in
  let* var = ident in
  let* formula = whitespace *> formula in
  ast var formula |> return

let formula =
  fix (fun formula ->
      let formula1 =
        parens formula <|> aformula
        |> opt (un_op "~" Ast.mnot)
        |> bin_op "&" Ast.mand |> bin_op "|" Ast.mor |> bin_op "->" Ast.mimpl
        |> bin_op "<->" Ast.miff
      in
      quantifier 'A' Ast.any formula
      <|> quantifier 'E' Ast.exists formula
      <|> formula1 )

let kw kw ast = string kw *> whitespace *> return ast

let kw1 kw ast p1 =
  let* _ = string kw <* whitespace in
  let* p1 = p1 in
  ast p1 |> return

let kw2 kw ast p1 p2 =
  let* _ = string kw <* whitespace in
  let* p1 = p1 in
  ast p1 p2

let kw3 kw ast p1 p2 p3 =
  let* _ = string kw <* whitespace in
  let* p1 = p1 in
  let* p2 = p2 in
  let* p3 = p3 in
  ast p1 p2 p3 |> return

let def =
  let* name = string "let" *> whitespace *> ident <* whitespace in
  let* params = many (whitespace *> ident) in
  let* body = whitespace *> char '=' *> whitespace *> formula in
  Ast.def name params body |> return

let stmt =
  kw1 "eval" Ast.eval formula
  <|> kw3 "let" Ast.def (ident <* whitespace)
        (many (whitespace *> ident))
        (whitespace *> char '=' *> whitespace *> formula)
  <|> kw1 "dump" Ast.dump formula
  <|> kw1 "parse" Ast.parse formula
  <|> kw "list" (Ast.list ())
  <|> kw "help" (Ast.help ())

let parse_formula str = parse_string ~consume:All formula str

let parse str = parse_string ~consume:All stmt str
