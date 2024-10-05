(** Copyright 2024, MacadamiaSolver. *)

(* SPDX-License-Identifier: MIT *)

type varname = string

type predname = string

type term =
  | Var of varname
  | Const of int
  | Add of term * term
  | Mul of int * term

type formula =
  | Pred of predname * term list
  | Equals of term * term
  | Mnot of formula
  | Mand of formula * formula
  | Mor of formula * formula
  | Mimpl of formula * formula
  | Exists of varname * formula
  | Any of varname * formula

type stmt =
  | Def of string * varname list * formula
  | Eval of formula
  | Dump of formula

val var : varname -> term

val const : int -> term

val add : term -> term -> term

val mul : int -> term -> term

val pred : predname -> term list -> formula

val equals : term -> term -> formula

val mnot : formula -> formula

val mand : formula -> formula -> formula

val mor : formula -> formula -> formula

val mimpl : formula -> formula -> formula

val exists : varname -> formula -> formula

val any : varname -> formula -> formula

val def : string -> varname list -> formula -> stmt

val eval : formula -> stmt

val dump : formula -> stmt

val string_of_term : term -> string

val string_of_formula : formula -> string

val string_of_stmt : stmt -> string
