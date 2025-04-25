(** Copyright 2024, MacadamiaSolver. *)

(* SPDX-License-Identifier: MIT *)

type varname = string
type predname = string

type term =
  | Var of varname
  | Const of int
  | Add of term * term
  | Mul of int * term
  | Pow of int * term
[@@deriving variants]

type formula =
  | True
  | False
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
  | Exists of varname list * formula
  | Any of varname list * formula
[@@deriving variants]

type stmt =
  | Def of string * varname list * formula
  | Defr of string * Regex.t
  | Eval of formula
  | Evalm of formula
  | Dump of formula
  | Parse of formula
  | List
  | Help
[@@deriving variants]

val pp_term : Format.formatter -> term -> unit
val pp_formula : Format.formatter -> formula -> unit
val quantifier_ast_exn : formula -> varname list -> formula -> formula
val binconj_ast_exn : formula -> formula -> formula -> formula
val tfold : ('acc -> term -> 'acc) -> 'acc -> term -> 'acc
val fold : ('acc -> formula -> 'acc) -> ('acc -> term -> 'acc) -> 'acc -> formula -> 'acc
val for_some : (formula -> bool) -> (term -> bool) -> formula -> bool
val for_all : (formula -> bool) -> (term -> bool) -> formula -> bool
val map : (formula -> formula) -> (term -> term) -> formula -> formula
