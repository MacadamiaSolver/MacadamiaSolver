(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

open Angstrom

let is_whitespace = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let whitespace = take_while is_whitespace
let whitespace1 = take_while1 is_whitespace

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let const = take_while1 is_digit >>| int_of_string >>| Ast.const

let is_idschar = function
  | 'a' .. 'z' | '_' -> true
  | _ -> false
;;

let is_idchar = function
  | 'a' .. 'z' | '_' | '0' .. '9' -> true
  | _ -> false
;;

let token p = whitespace *> p <* whitespace

let ident =
  let ident' =
    let* a = satisfy is_idschar in
    let* b = take_while is_idchar in
    String.make 1 a ^ b |> return
  in
  token ident' <?> "expected identifier satisfying [a-z_0-9][a-z_0-9]*"
;;

let var = token ident >>| Ast.var

let integer =
  token (take_while1 is_digit) >>| int_of_string <?> "expected constant integer value"
;;

let parens p = token (char '(') *> p <* token (char ')')

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= go
;;

let un_op op ast p = token (string op) *> p >>| ast

let bin_op op ast p =
  let op = token (string op) *> return ast in
  chainl1 p op
;;

let opt q p = q p <|> p

let mul term =
  let* c = integer in
  let* body = term in
  Ast.mul c body |> return
;;

let pow term =
  let* c = integer <* token (string "**") in
  let* body = term in
  Ast.pow c body |> return
;;

let term =
  fix (fun term ->
    parens term <|> const <|> var |> opt pow |> opt mul |> bin_op "+" Ast.add)
;;

let pred =
  let* name = ident in
  let* params = term |> many in
  Ast.pred name params |> return
;;

let pred_op op ast =
  let* a = term in
  let* _ = token (string op) in
  let* b = term in
  ast a b |> return
;;

let aformula =
  pred_op "=" Ast.eq
  <|> pred_op "!=" Ast.neq
  <|> pred_op "<" Ast.lt
  <|> pred_op ">" Ast.gt
  <|> pred_op "<=" Ast.leq
  <|> pred_op ">=" Ast.geq
  <|> pred
  <?> "expected atomic formula"
;;

let quantifier sym ast formula =
  let* _ = char sym in
  let* var = ident in
  let* formula = formula in
  ast [ var ] formula |> return
;;

let formula =
  fix (fun formula ->
    let formula1 =
      parens formula
      <|> aformula
      |> opt (un_op "~" Ast.mnot)
      |> bin_op "&" Ast.mand
      |> bin_op "|" Ast.mor
      |> bin_op "->" Ast.mimpl
      |> bin_op "<->" Ast.miff
    in
    quantifier 'A' Ast.any formula <|> quantifier 'E' Ast.exists formula <|> formula1)
  <?> "expected formula"
;;

let stmt =
  let* kw = ident in
  match kw with
  | "eval" -> lift Ast.eval formula
  | "evalm" -> lift Ast.evalm formula
  | "evalsemenov" -> lift Ast.evalsemenov formula
  | "evalsemenovm" -> lift Ast.evalsemenov formula
  | "let" -> lift3 Ast.def ident (many ident) (token (char '=') *> formula)
  | "letr" ->
    lift2
      Ast.defr
      ident
      (token (char '=')
       *> (take_while (fun c -> is_whitespace c |> not)
           >>| Regex.of_string
           >>| Result.get_ok))
  | "dump" -> lift Ast.dump formula
  | "parse" -> lift Ast.parse formula
  | "list" -> return Ast.list
  | "help" -> return Ast.help
  | _ -> Format.sprintf "Unknown keyword %s" kw |> fail
;;

let parse_formula str = parse_string ~consume:Prefix formula str
let parse str = parse_string ~consume:Prefix stmt str

let%expect_test "parse simple formula" =
  Format.printf "%a" Ast.pp_formula (parse_formula {|Ax x = 2 | x != 2|} |> Result.get_ok);
  [%expect {| (Ax ((x = 2) | (x != 2))) |}]
;;

let%expect_test "parse multiple quantifier formula" =
  Format.printf "%a" Ast.pp_formula (parse_formula {|ExEy z = 5x + 3y|} |> Result.get_ok);
  [%expect {| (Ex (Ey (z = ((5 * x) + (3 * y))))) |}]
;;

let%expect_test "parse long chain" =
  Format.printf
    "%a"
    Ast.pp_formula
    (parse_formula {|x = 2 & y = 3 & z = 4 & a = 1 & b = 5|} |> Result.get_ok);
  [%expect {| (((((x = 2) & (y = 3)) & (z = 4)) & (a = 1)) & (b = 5)) |}]
;;

let%expect_test "parse parens and complex priorities" =
  Format.printf
    "%a"
    Ast.pp_formula
    (parse_formula
       {|a = 1 & b = 2 & (t + 2(z + 3q) + (2d + 5w) >= 15 | (Ex Ey x + y = 15))|}
     |> Result.get_ok);
  [%expect
    {| (((a = 1) & (b = 2)) & ((((t + (2 * (z + (3 * q)))) + ((2 * d) + (5 * w))) >= 15) | (Ex (Ey ((x + y) = 15))))) |}]
;;
