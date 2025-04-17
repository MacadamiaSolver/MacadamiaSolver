open Angstrom

let is_whitespace = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let whitespace = take_while is_whitespace
let whitespace1 = take_while1 is_whitespace

let is_symbolchar = function
  | 'a' .. 'z'
  | 'A' .. 'Z'
  | '0' .. '9'
  | '+'
  | '-'
  | '/'
  | '*'
  | '='
  | '%'
  | '?'
  | '!'
  | '.'
  | '$'
  | '~'
  | '&'
  | '^'
  | '<'
  | '>'
  | '@'
  | '_' -> true
  | _ -> false
;;

let token p =
  let p1 = whitespace *> p <* whitespace in
  let comment = whitespace *> char ';' <* take_while (fun c -> c <> '\n') in
  comment *> p1 <|> p1
;;

let parens p = (char '(' |> token) *> p <* (char ')' |> token)

let symbol =
  let symbol' =
    let* head = satisfy (fun c -> is_symbolchar c && is_digit c |> not) in
    let* tail = take_while is_symbolchar in
    return (Char.escaped head ^ tail)
  in
  token symbol'
;;

let%expect_test "symbols" =
  parse_string ~consume:Prefix symbol "symbol" |> Result.get_ok |> Format.printf "%s@.";
  parse_string ~consume:Prefix symbol "SYMBOL" |> Result.get_ok |> Format.printf "%s@.";
  parse_string ~consume:Prefix symbol "symbol123" |> Result.get_ok |> Format.printf "%s@.";
  parse_string ~consume:Prefix symbol "s/%o!=*q9<@3*"
  |> Result.get_ok
  |> Format.printf "%s@.";
  [%expect
    {|
    symbol
    SYMBOL
    symbol123
    s/%o!=*q9<@3*
    |}]
;;

let numeral =
  let numeral' =
    let zero_numeral = char '0' *> return 0 in
    let non_zero_numeral =
      let* head = satisfy (fun c -> is_digit c && c <> '0') in
      let* tail = take_while is_digit in
      return (Char.escaped head ^ tail |> int_of_string)
    in
    zero_numeral <|> non_zero_numeral
  in
  token numeral'
;;

let%expect_test "numerals" =
  parse_string ~consume:Prefix numeral "1234" |> Result.get_ok |> Format.printf "%d@.";
  parse_string ~consume:Prefix numeral "999999" |> Result.get_ok |> Format.printf "%d@.";
  [%expect
    {|
    1234
    999999
    |}]
;;

(* S-expressions. *)

type constant =
  | Numeric of int (* this one is currently used for decimal, binary, hexademical too *)
  | String of string
[@@deriving show, variants]

let decimal = fail "unimplemented"
let hexademical = fail "unimplemented"
let binary = fail "unimplemented"
let string = fail "unimplemented"

let constant =
  let numeric =
    let* v = numeral <|> decimal <|> hexademical <|> binary in
    numeric v |> return
  in
  let string = string in
  numeric <|> string
;;

(* Identifiers. *)

let identifier =
  let simple_identifier =
    let* symbol = symbol in
    symbol |> return
  in
  let indexed_identifier' =
    let index = numeral >>| string_of_int <|> symbol in
    let* symbol = char '_' *> whitespace *> symbol <* whitespace in
    let* indices = many (index <* whitespace) in
    String.concat "\\" (symbol :: indices) |> return
  in
  let indexed_identifier = parens indexed_identifier' in
  simple_identifier <|> indexed_identifier <?> "expected identifier"
;;

let%expect_test "identifiers" =
  parse_string ~consume:Prefix identifier "simple_identifier"
  |> Result.get_ok
  |> Format.printf "%s";
  parse_string ~consume:Prefix identifier "(_ complex_identifier 1 2)"
  |> Result.get_ok
  |> Format.printf "%s";
  [%expect {| simple_identifiercomplex_identifier\1\2 |}]
;;

(* Sorts. *)

type sort = Sort of string * sort list [@@deriving show, variants]

let sort =
  fix (fun sort' ->
    let simple_sort =
      let* identifier = identifier in
      sort identifier [] |> return
    in
    let multiple_sort' =
      let* identifier = identifier <* whitespace in
      let* sorts = many (sort' <* whitespace) in
      sort identifier sorts |> return
    in
    let multiple_sort = parens multiple_sort' in
    simple_sort <|> multiple_sort <?> "expected sort")
;;

let%expect_test "sorts" =
  parse_string ~consume:Prefix sort "SimpleSort"
  |> Result.get_ok
  |> Format.printf "%a@." pp_sort;
  parse_string ~consume:Prefix sort "(MultipleSort (Sort1) (Sort2))"
  |> Result.get_ok
  |> Format.printf "%a@." pp_sort;
  parse_string
    ~consume:Prefix
    sort
    "(Sort1 (Sort2 (Sort3) (Sort4 (Sort5)) (Sort6)) (Sort7) (Sort8 (Sort9)))"
  |> Result.get_ok
  |> Format.printf "%a@." pp_sort;
  [%expect
    {|
    (Smtlib.Sort ("SimpleSort", []))
    (Smtlib.Sort ("MultipleSort",
       [(Smtlib.Sort ("Sort1", [])); (Smtlib.Sort ("Sort2", []))]))
    (Smtlib.Sort ("Sort1",
       [(Smtlib.Sort ("Sort2",
           [(Smtlib.Sort ("Sort3", []));
             (Smtlib.Sort ("Sort4", [(Smtlib.Sort ("Sort5", []))]));
             (Smtlib.Sort ("Sort6", []))]
           ));
         (Smtlib.Sort ("Sort7", []));
         (Smtlib.Sort ("Sort8", [(Smtlib.Sort ("Sort9", []))]))]
       ))
    |}]
;;

(* Terms. *)

type term =
  | SpecConstant of constant
  | Let' of (string * term) list * term
  | Forall of (string * sort) list * term
  | Exists of (string * sort) list * term
  | Match of term * (string list * term) list
  | Apply of string * sort option * term list
[@@deriving show, variants]

let term =
  fix (fun term ->
    let _var_binding = lift2 (fun a b -> a, b) symbol term |> parens in
    let sorted_var = lift2 (fun a b -> a, b) symbol sort |> parens in
    let qualidentifier =
      let simple_identifier =
        let* identifier = identifier in
        (identifier, None) |> return
      in
      (* TODO: support "as" *)
      let complex_identifier = fail "unimplemented" in
      simple_identifier <|> complex_identifier
    in
    let simple_term =
      let constant = constant >>| specconstant in
      let apply0 =
        let* identifier, sort = qualidentifier in
        apply identifier sort [] |> return
      in
      constant <|> apply0
    in
    let complex_term' =
      let* keyword = take_while1 is_symbolchar <* whitespace in
      match keyword with
      | "let" -> fail "unimplemented"
      | "exists" ->
        let* vars = many1 (sorted_var <* whitespace) |> parens in
        let* term = term in
        exists vars term |> return
      | "forall" ->
        let* vars = many1 (sorted_var <* whitespace) |> parens in
        let* term = term in
        forall vars term |> return
      | _ -> fail "unknown keyword"
    in
    let apply_term' =
      let* identifier, sort = qualidentifier in
      let* terms = many1 term in
      apply identifier sort terms |> return
    in
    let apply_term = apply_term' |> parens in
    let complex_term = parens complex_term' in
    simple_term <|> complex_term <|> apply_term <?> "expected term")
;;

let%expect_test "terms" =
  parse_string ~consume:All term {|(not (= (+ (* x0 11) (* x1 13)) P))|}
  |> Result.get_ok
  |> Format.printf "%a@." pp_term;
  [%expect
    {|
    (Smtlib.Apply ("not", None,
       [(Smtlib.Apply ("=", None,
           [(Smtlib.Apply ("+", None,
               [(Smtlib.Apply ("*", None,
                   [(Smtlib.Apply ("x0", None, []));
                     (Smtlib.SpecConstant (Smtlib.Numeric 11))]
                   ));
                 (Smtlib.Apply ("*", None,
                    [(Smtlib.Apply ("x1", None, []));
                      (Smtlib.SpecConstant (Smtlib.Numeric 13))]
                    ))
                 ]
               ));
             (Smtlib.Apply ("P", None, []))]
           ))
         ]
       ))
    |}]
;;

(* Commands. *)

type command =
  | SetLogic of string
  | SetOption of string
  | SetInfo of string (* temporary stub *)
  | DeclareSort of string * int
  | DefineSort of string * string list * sort
  | DeclareFun of string * sort list * sort
  (*| DefineFun of string * sorted * var list * sort * term*)
  | Push of int
  | Pop of int
  | Assert' of term (* Renamed not to clash with OCaml keywords. *)
  | CheckSat
  | GetAssertions
  | GetModel
  | GetProof
  | GetUnsatCore
  | GetValue of term list
  | GetAssignment
  (*| GetOption of keyword*)
  (*| GetInfo of info flag *)
  | Exit
[@@deriving show, variants]

let command =
  let result' =
    let* keyword = take_while is_symbolchar |> token in
    match keyword with
    | "set-logic" -> symbol >>| setlogic
    | "set-info" ->
      let* v = take_while (fun c -> c <> ')') in
      setinfo v |> return
    | "set-option" ->
      let* v = take_while (fun c -> c <> ')') in
      setoption v |> return
    | "declare-fun" ->
      let* name = symbol in
      let* arg_sorts = many sort |> parens in
      let* ret_sort = sort in
      declarefun name arg_sorts ret_sort |> return
    | "push" -> numeral >>| push
    | "pop" -> numeral >>| pop
    | "assert" -> term >>| assert'
    | "check-sat" -> return checksat
    | "get-assertions" -> return getassertions
    | "get-model" -> return getmodel
    | "get-proof" -> return getproof
    | "get-unsat-core" -> return getunsatcore
    | "get-assignment" -> return getassignment
    | "get-value" -> many1 (term <* whitespace) >>| getvalue
    | "exit" -> return exit
    | _ -> fail "unknown command"
  in
  parens result'
;;

let script = many command
let parse = parse_string ~consume:Prefix script

let%expect_test "check-sat" =
  let script =
    parse
      {|
        (set-info :smt-lib-version 2.6)
        (set-logic LIA)
        (set-info :source |
        Generated by: Vojtěch Havlena, Michal Hečko, Lukáš Holík, Ondřej Lengál
        Generated on: 2025-02-13
        Target solver: Amaya
        Instances of the Frobenius coin problem with two coins involving multiple
        quantifier alternations that seem difficult for modern SMT solvers.
        |)
        (set-info :license "https://creativecommons.org/licenses/by/4.0/")
        (set-info :category "crafted")
        (set-info :status sat)

        (declare-fun P () Int)
        (assert (and (<= 0 P) (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 7) (* x1 11)) P)))) (forall ((R Int)) (=> (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 7) (* x1 11)) R)))) (<= R P)))))
        (check-sat)
        (exit)
      |}
    |> Result.get_ok
  in
  Format.printf
    "%a@."
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n") pp_command)
    script;
  [%expect
    {|
    (Smtlib.SetInfo ":smt-lib-version 2.6")
    (Smtlib.SetLogic "LIA")
    (Smtlib.SetInfo
                                                                       ":source |\n        Generated by: Vojt\196\155ch Havlena, Michal He\196\141ko, Luk\195\161\197\161 Hol\195\173k, Ond\197\153ej Leng\195\161l\n        Generated on: 2025-02-13\n        Target solver: Amaya\n        Instances of the Frobenius coin problem with two coins involving multiple\n        quantifier alternations that seem difficult for modern SMT solvers.\n        |")
    (
    Smtlib.SetInfo ":license \"https://creativecommons.org/licenses/by/4.0/\"")
    (
    Smtlib.SetInfo ":category \"crafted\"")
    (Smtlib.SetInfo ":status sat")
    (
    Smtlib.DeclareFun ("P", [], (Smtlib.Sort ("Int", []))))
    (Smtlib.Assert'
                                                               (Smtlib.Apply (
                                                                  "and", None,
                                                                  [(Smtlib.Apply (
                                                                      "<=", None,
                                                                      [(Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        0));
                                                                        (
                                                                        Smtlib.Apply (
                                                                        "P",
                                                                        None,
                                                                        []))]
                                                                      ));
                                                                    (Smtlib.Forall (
                                                                       [("x0",
                                                                        (Smtlib.Sort (
                                                                        "Int",
                                                                        [])));
                                                                        ("x1",
                                                                        (Smtlib.Sort (
                                                                        "Int",
                                                                        [])))],
                                                                       (Smtlib.Apply (
                                                                        "=>",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "and",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "<=",
                                                                        None,
                                                                        [(Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        0));
                                                                        (Smtlib.Apply (
                                                                        "x0",
                                                                        None,
                                                                        []))]));
                                                                        (Smtlib.Apply (
                                                                        "<=",
                                                                        None,
                                                                        [(Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        0));
                                                                        (Smtlib.Apply (
                                                                        "x1",
                                                                        None,
                                                                        []))]))]
                                                                        ));
                                                                        (Smtlib.Apply (
                                                                        "not",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "=",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "+",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "*",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "x0",
                                                                        None,
                                                                        []));
                                                                        (Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        7))]));
                                                                        (Smtlib.Apply (
                                                                        "*",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "x1",
                                                                        None,
                                                                        []));
                                                                        (Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        11))]))]
                                                                        ));
                                                                        (Smtlib.Apply (
                                                                        "P",
                                                                        None,
                                                                        []))]))]
                                                                        ))]))
                                                                       ));
                                                                    (Smtlib.Forall (
                                                                       [("R",
                                                                        (Smtlib.Sort (
                                                                        "Int",
                                                                        [])))],
                                                                       (Smtlib.Apply (
                                                                        "=>",
                                                                        None,
                                                                        [(Smtlib.Forall (
                                                                        [("x0",
                                                                        (Smtlib.Sort (
                                                                        "Int",
                                                                        [])));
                                                                        ("x1",
                                                                        (Smtlib.Sort (
                                                                        "Int",
                                                                        [])))],
                                                                        (Smtlib.Apply (
                                                                        "=>",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "and",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "<=",
                                                                        None,
                                                                        [(Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        0));
                                                                        (Smtlib.Apply (
                                                                        "x0",
                                                                        None,
                                                                        []))]));
                                                                        (Smtlib.Apply (
                                                                        "<=",
                                                                        None,
                                                                        [(Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        0));
                                                                        (Smtlib.Apply (
                                                                        "x1",
                                                                        None,
                                                                        []))]))]
                                                                        ));
                                                                        (Smtlib.Apply (
                                                                        "not",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "=",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "+",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "*",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "x0",
                                                                        None,
                                                                        []));
                                                                        (Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        7))]));
                                                                        (Smtlib.Apply (
                                                                        "*",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "x1",
                                                                        None,
                                                                        []));
                                                                        (Smtlib.SpecConstant
                                                                        (Smtlib.Numeric
                                                                        11))]))]
                                                                        ));
                                                                        (Smtlib.Apply (
                                                                        "R",
                                                                        None,
                                                                        []))]))]
                                                                        ))]))));
                                                                        (Smtlib.Apply (
                                                                        "<=",
                                                                        None,
                                                                        [(Smtlib.Apply (
                                                                        "R",
                                                                        None,
                                                                        []));
                                                                        (Smtlib.Apply (
                                                                        "P",
                                                                        None,
                                                                        []))]))]
                                                                        ))
                                                                       ))
                                                                    ]
                                                                  )))
    Smtlib.CheckSat
    Smtlib.Exit
    |}]
;;
(*
   (set-info :smt-lib-version 2.6)
    (set-info :source |
    Generated by: Vojtěch Havlena, Michal Hečko, Lukáš Holík, Ondřej Lengál
    Generated on: 2025-02-13
    Target solver: Amaya
    Instances of the Frobenius coin problem with two coins involving multiple
    quantifier alternations that seem difficult for modern SMT solvers.
    |)
    (set-info :license "https://creativecommons.org/licenses/by/4.0/")
    (set-info :category "crafted")
    (set-info :status sat)
    (declare-fun P () Int)
*)
