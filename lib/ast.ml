(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

type varname = string

type predname = string

type term =
  | Var of varname
  | Const of int
  | Add of term * term
  | Mul of int * term

type formula =
  | Pred of predname * term list
  | Eq of term * term
  | Neq of term * term
  | Lt of term * term
  | Gt of term * term
  | Leq of term * term
  | Geq of term * term
  | Mnot of formula
  | Mand of formula * formula
  | Mor of formula * formula
  | Mimpl of formula * formula
  | Miff of formula * formula
  | Exists of varname * formula
  | Any of varname * formula

type stmt =
  | Def of string * varname list * formula
  | Eval of formula
  | Dump of formula
  | Parse of formula
  | List
  | Help

let var x = Var x

let const x = Const x

let add x y = Add (x, y)

let mul x y = Mul (x, y)

let pred n p = Pred (n, p)

let eq x y = Eq (x, y)

let neq x y = Neq (x, y)

let lt x y = Lt (x, y)

let gt x y = Gt (x, y)

let leq x y = Leq (x, y)

let geq x y = Geq (x, y)

let mnot x = Mnot x

let mand x y = Mand (x, y)

let mor x y = Mor (x, y)

let mimpl x y = Mimpl (x, y)

let miff x y = Miff (x, y)

let exists x y = Exists (x, y)

let any x y = Any (x, y)

let def x p f = Def (x, p, f)

let eval f = Eval f

let dump f = Dump f

let parse f = Parse f

let list () = List

let help () = Help

let rec pp_term ppf = function
  | Var n -> Format.fprintf ppf "%s" n
  | Const n -> Format.fprintf ppf "%d" n
  | Add (a, b) -> Format.fprintf ppf "(%a + %a)" pp_term a pp_term b
  | Mul (a, b) -> Format.fprintf ppf "(%d * %a)" a pp_term b

let rec pp_formula ppf = function
  | Pred (a, b) -> Format.fprintf ppf "(P %s %a)" a (Format.pp_print_list pp_term) b
  | Eq (a, b) -> Format.fprintf ppf "(%a = %a)" pp_term a pp_term b
  | Neq (a, b) -> Format.fprintf ppf "(%a != %a)" pp_term a pp_term b
  | Lt (a, b) -> Format.fprintf ppf "(%a < %a)" pp_term a pp_term b
  | Gt (a, b) -> Format.fprintf ppf "(%a > %a)" pp_term a pp_term b
  | Leq (a, b) -> Format.fprintf ppf "(%a <= %a)" pp_term a pp_term b
  | Geq (a, b) -> Format.fprintf ppf "(%a >= %a)" pp_term a pp_term b
  | Mnot (a) -> Format.fprintf ppf "(~ %a)" pp_formula a
  | Mand (a, b) -> Format.fprintf ppf "(%a & %a)" pp_formula a pp_formula b
  | Mor (a, b) -> Format.fprintf ppf "(%a | %a)" pp_formula a pp_formula b
  | Mimpl (a, b) -> Format.fprintf ppf "(%a -> %a)" pp_formula a pp_formula b
  | Miff (a, b) -> Format.fprintf ppf "(%a <-> %a)" pp_formula a pp_formula b
  | Exists (a, b) -> Format.fprintf ppf "(E%s %a)" a pp_formula b
  | Any (a, b) -> Format.fprintf ppf "(A%s %a)" a pp_formula b

