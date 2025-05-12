(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

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

let is_idschar = function
  | 'a' .. 'z' | '_' -> true
  | _ -> false
;;

let is_idchar = function
  | 'a' .. 'z' | '_' | '0' .. '9' -> true
  | _ -> false
;;

let is_opchar = function
  | '='
  | '<'
  | '>'
  | '!'
  | '-'
  | '+'
  | '~'
  | '|'
  | '&'
  | '%'
  | '@'
  | '#'
  | '$'
  | '*'
  | '^'
  | '/'
  | '\\' -> true
  | _ -> false
;;

let token p = whitespace *> p <* whitespace
let const = token (take_while1 is_digit) >>| int_of_string >>| Ast.const

let ident =
  let ident' =
    let* a = satisfy is_idschar in
    let* b = take_while is_idchar <?> "Identifier can only contain symbols [a-z_0-9]" in
    String.make 1 a ^ b |> return
  in
  token ident' <?> "identifier"
;;

let op = take_while is_opchar |> token
let var = token ident >>| Ast.var
let integer = token (take_while1 is_digit) >>| int_of_string <?> "Integers "
let parens p = token (char '(') *> p <* (token (char ')') <?> "expected ')'")

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

let term =
  let mul term =
    let lmul =
      let* c = integer <* token (string "*") in
      let* body = term in
      Ast.mul c body |> return
    in
    let rmul =
      let* body = term <* token (string "*") in
      let* c = integer in
      Ast.mul c body |> return
    in
    lmul <|> rmul
  in
  let pow term =
    let* c = integer <* token (string "**") in
    let* body = term in
    Ast.pow c body |> return
  in
  fix (fun term ->
    let aterm =
      let* c = peek_char_fail in
      match c with
      | c when is_idschar c -> var
      | c when is_digit c -> const
      | '(' -> parens term
      | _ -> fail "Expected term (i.e 'z * 5 + 2 + 3 * y' or '2**y')"
    in
    pow aterm <|> mul aterm <|> aterm |> bin_op "+" Ast.add)
  <?> "term"
;;

let aformula =
  let pred =
    let* name = ident in
    let* params = term |> many1 in
    Ast.pred name params |> return
  in
  let pred_op =
    let* a = term in
    let* op = op in
    let* ast =
      match op with
      | "=" -> return Ast.eq
      | "!=" -> return Ast.neq
      | "<" -> return Ast.lt
      | ">" -> return Ast.gt
      | "<=" -> return Ast.leq
      | ">=" -> return Ast.geq
      | "~=" | "<>" ->
        Format.sprintf "Unknown operator ~=, probably you've meant !=" |> fail
      | "==" -> Format.sprintf "Unknown operator ==, probably you've meant =" |> fail
      | s -> Format.sprintf "Unknown operator %s" s |> fail
    in
    let* b = term in
    ast a b |> return
  in
  pred <|> pred_op <?> "atomic formula"
;;

let formula =
  let quantifier sym ast formula =
    let* _ = char sym in
    let* var = ident in
    let* formula = formula in
    ast [ var ] formula |> return
  in
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
  <?> "formula"
;;

let stmt =
  let* kw = ident in
  match kw with
  | "eval" -> lift Ast.eval formula
  | "evalm" -> lift Ast.evalm formula
  | "evalsemenovm" -> lift Ast.eval formula (* stub *)
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
  | _ -> Format.sprintf "Unknown command %s" kw |> fail
;;

let parse_formula str = parse_string ~consume:All formula str
let parse str = parse_string ~consume:All stmt str

let%expect_test "parse simple formula" =
  Format.printf "%a" Ast.pp_formula (parse_formula {|Ax x = 2 | x != 2|} |> Result.get_ok);
  [%expect {| (Ax ((x = 2) | (x != 2))) |}]
;;

let%expect_test "parse multiple quantifier formula" =
  Format.printf "%a" Ast.pp_formula (parse_formula {|ExEy z = 5*x + 3*y|} |> Result.get_ok);
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
       {|a = 1 & b = 2 & (t + 2*(z + 3*q) + (2*d + 5*w) >= 15 | (Ex Ey x + y = 15))|}
     |> Result.get_ok);
  [%expect
    {| (((a = 1) & (b = 2)) & ((((t + (2 * (z + (3 * q)))) + ((2 * d) + (5 * w))) >= 15) | (Ex (Ey ((x + y) = 15))))) |}]
;;

let%expect_test "unknown_operator" =
  Format.printf "%s\n" (parse_formula {|x % 5|} |> Result.get_error);
  Format.printf "%s\n" (parse_formula {|x <> 5|} |> Result.get_error);
  Format.printf "%s\n" (parse_formula {|x == 5|} |> Result.get_error);
  [%expect
    {|
    formula > atomic formula: Unknown operator %
    formula > atomic formula: Unknown operator ~=, probably you've meant !=
    formula > atomic formula: Unknown operator ==, probably you've meant =
    |}]
;;
