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
  | '#'
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
  many comment *> p1
;;

let parens p = (char '(' |> token) *> p <* (char ')' |> token)

let symbol =
  let symbol' =
    let* head = satisfy (fun c -> is_symbolchar c && is_digit c |> not) in
    let* tail = take_while is_symbolchar in
    return (Char.escaped head ^ tail)
  in
  token (char '|' *> symbol' <* char '|' <|> symbol')
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

let decimal = fail "decimals are unimplemented"
let hexademical = fail "hexadecimals are unimplemented"
let binary = fail "binary literals are unimplemented"
let string = fail "strings are unimplemented"

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
  simple_identifier <|> indexed_identifier <?> "identifier"
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
    simple_sort <|> multiple_sort <?> "sort")
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
      let complex_identifier = fail "'as' is unimplemented" in
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
      | "let" ->
        let* bindings =
          many1 (lift2 (fun a b -> a, b) identifier term |> parens) |> parens
        in
        let* term = term in
        let' bindings term |> return
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
    simple_term <|> complex_term <|> apply_term <?> "term")
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
    | "set-logic" -> symbol <?> "set-logic name" >>| setlogic
    | "set-info" ->
      let* v = take_while (fun c -> c <> ')') in
      setinfo v |> return
    | "set-option" ->
      let* v = take_while (fun c -> c <> ')') in
      setoption v |> return
    | "declare-fun" ->
      let* name = symbol <?> "declare-fun name" in
      let* arg_sorts = many sort |> parens <?> "declare-fun argument sorts" in
      let* ret_sort = sort <?> "declare-fun return value sort" in
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
    | _ as command ->
      Format.sprintf "unknown or unsupported SMT-lib command %s" command |> fail
  in
  parens result'
;;

let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []
;;

let script =
  let* commands = many1 command in
  let* at_end = at_end_of_input in
  if at_end
  then return commands
  else
    let* remaining = 0 -- 32 |> List.rev |> List.map (fun n -> peek_string n) |> choice in
    let* _ =
      command
      <?> (remaining
           |> String.map (fun c -> if c = '\n' then ' ' else c)
           |> Format.sprintf "unable to parse '%s' ")
    in
    return []
;;

let parse s = parse_string ~consume:Prefix script s

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

let ( let* ) = Result.bind
let return = Result.ok
let fail = Result.error

let rec fmap f = function
  | [] -> return []
  | h :: tl ->
    let* h = f h in
    let* tl = fmap f tl in
    h :: tl |> return
;;

let rec to_term = function
  | Apply (f, _, ts) ->
    let arg n =
      let* arg =
        List.nth_opt ts n
        |> Option.to_result ~none:(Format.sprintf "missing %d argument" n)
      in
      arg |> to_term
    in
    let ct ast =
      match ts with
      | t :: tl ->
        let* t = to_term t in
        List.fold_left
          (fun acc t ->
             let* f = to_term t in
             let* acc = acc in
             ast acc f |> return)
          (t |> return)
          tl
      | [] -> failwith "expected at least 1 argument"
    in
    let tiop ast =
      let* t1 = arg 0 in
      let* t2 = arg 1 in
      match t1, t2 with
      | Ast.Const d, _ -> ast d t2 |> return
      | _, Ast.Const d -> ast d t1 |> return
      | _ ->
        "multiplication operator is only supported between a constant and a term" |> fail
    in
    (match%pcre f with
     (* LIA *)
     | {|\+|} -> ct Ast.add
     | {|\*|} -> tiop Ast.mul
     (* EIA *)
     | "exp" ->
       let* t1 = arg 0 in
       let* t2 = arg 1 in
       (match t1, t2 with
        | Ast.Const d, _ ->
          if d = 2 then Ast.pow d t2 |> return else fail "only base two is supported"
        | _ -> fail "only exponents in 2**<var> syntax are supported")
     (* BV *)
     | "bv2nat" ->
       let* t = arg 0 in
       return t
     | "bvadd" -> ct Ast.add
     | "bvand" -> ct Ast.bvand
     | "bvor" -> ct Ast.bvor
     | "bvxor" -> ct Ast.bvxor
     | {|int2bv\\\d+|} ->
       let* t = arg 0 in
       return t
     | _ -> Ast.var f |> return)
  | SpecConstant c ->
    (match c with
     | Numeric d -> Ast.const d |> return
     | _ -> "unknown constant type" |> Result.error)
  | _ as t -> Format.asprintf "expected term, found %a" pp_term t |> fail
;;

let rec to_formula = function
  | Forall (vars, t) ->
    let vars = vars |> List.map fst in
    let* f = to_formula t in
    Ast.any vars f |> return
  | Exists (vars, t) ->
    let vars = vars |> List.map fst in
    let* f = to_formula t in
    Ast.exists vars f |> return
  | Let' (bindings, f) ->
    assert (List.length bindings >= 1);
    let* f = to_formula f in
    Ast.map
      (function
        | Ast.Pred (x, _) as f ->
          (match List.find_opt (fun (var, _) -> x = var) bindings |> Option.map snd with
           | Some binding ->
             binding
             |> (fun x ->
             Format.printf "%a\n%!\n%!" pp_term x;
             x)
             |> to_formula
             |> Result.get_ok
           | None -> f)
        | t -> t)
      (function
        | Ast.Var x as t ->
          (match List.find_opt (fun (var, _) -> x = var) bindings |> Option.map snd with
           | Some binding ->
             binding
             |> (fun x ->
             Format.printf "%a\n%!\n%!" pp_term x;
             x)
             |> to_term
             |> Result.get_ok
           | None -> t)
        | t -> t)
      f
    |> return
  | Apply (f, _, ts) ->
    let arg n =
      List.nth_opt ts n |> Option.to_result ~none:(Format.sprintf "missing %d argument" n)
    in
    let argf n =
      let* f = arg n in
      f |> to_formula
    in
    let argt n =
      let* t = arg n in
      t |> to_term
    in
    let fop1 ast =
      assert (List.length ts = 1);
      let* f1 = argf 0 in
      ast f1 |> return
    in
    let fop2 ast =
      assert (List.length ts = 2);
      let* f1 = argf 0 in
      let* f2 = argf 1 in
      ast f1 f2 |> return
    in
    let top2 ast =
      assert (List.length ts = 2);
      let* t1 = argt 0 in
      let* t2 = argt 1 in
      ast t1 t2 |> return
    in
    let cf ast =
      match ts with
      | t :: tl ->
        let* t = to_formula t in
        List.fold_left
          (fun acc t ->
             let* f = to_formula t in
             let* acc = acc in
             ast acc f |> return)
          (t |> return)
          tl
      | [] -> fail "expected at least 1 argument"
    in
    (match f with
     | "=" ->
       (match top2 Ast.eq with
        | Ok r -> r |> return
        | Error msg1 ->
          (match cf Ast.mand with
           | Ok r -> r |> return
           | Error msg2 ->
             Format.sprintf
               "'=' expected all arguments to be formulas or terms; if you meant term \
                the problem is '%s'; if you meant formulas the problem is '%s'"
               msg1
               msg2
             |> fail))
     | "<=" -> top2 Ast.leq
     | ">=" -> top2 Ast.geq
     | "<" -> top2 Ast.lt
     | ">" -> top2 Ast.gt
     | "not" -> fop1 Ast.mnot
     | "and" -> cf Ast.mand
     | "or" -> cf Ast.mor
     | "=>" -> fop2 Ast.mimpl
     (* BV *)
     | "bvule" -> top2 Ast.leq
     | "bvuge" -> top2 Ast.geq
     | "bvult" -> top2 Ast.lt
     | "bvugt" -> top2 Ast.gt
     | pred ->
       let* ts = ts |> fmap to_term in
       Ast.pred pred ts |> return)
    (* TODO: string is ignored *)
  | _ as term ->
    Format.asprintf "unimplemented SMT-lib construction: %a" pp_term term |> fail
;;

let%expect_test "Basic to term" =
  parse_string ~consume:Prefix term "(+ (* x0 7) (* x1 11) (* x5 15))"
  |> Result.get_ok
  |> to_term
  |> Result.get_ok
  |> Format.printf "%a@." Ast.pp_term;
  [%expect {| (((7 * x0) + (11 * x1)) + (15 * x5)) |}]
;;

let%expect_test "Exponent to term" =
  parse_string ~consume:Prefix term "(+ (exp 2 x) 15 y)"
  |> Result.get_ok
  |> to_term
  |> Result.get_ok
  |> Format.printf "%a@." Ast.pp_term;
  [%expect {| (((2 ** x) + 15) + y) |}]
;;

let%expect_test "Fail wrong base" =
  parse_string ~consume:Prefix term "(exp 3 x)"
  |> Result.get_ok
  |> to_term
  |> Result.get_error
  |> Format.printf "%s";
  [%expect {| only base two is supported |}]
;;

let%expect_test "Fail non-integer base" =
  parse_string ~consume:Prefix term "(exp x 3)"
  |> Result.get_ok
  |> to_term
  |> Result.get_error
  |> Format.printf "%s";
  [%expect {| only exponents in 2**<var> syntax are supported |}]
;;

let%expect_test "Basic formula" =
  parse_string
    ~consume:Prefix
    term
    {|(forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 7) (* x1 11)) R))))|}
  |> Result.get_ok
  |> to_formula
  |> Result.get_ok
  |> Format.printf "%a" Ast.pp_formula;
  [%expect {| (Ax0 x1 (((0 <= x0) & (0 <= x1)) -> (~ (((7 * x0) + (11 * x1)) = R)))) |}]
;;
