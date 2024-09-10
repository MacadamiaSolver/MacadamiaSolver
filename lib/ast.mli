(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

type varname = string

type term = Var of varname | Const of int | Add of term * term

type formula =
  | Equals of term * term
  | Mnot of formula
  | Mand of formula * formula
  | Mor of formula * formula
  | Mimpl of formula * formula
  | Exists of varname * formula
  | Any of varname * formula

val var : varname -> term

val const : int -> term

val add : term -> term -> term

val equals : term -> term -> formula

val mnot : formula -> formula

val mand : formula -> formula -> formula

val mor : formula -> formula -> formula

val mimpl : formula -> formula -> formula

val exists : varname -> formula -> formula

val any : varname -> formula -> formula

val string_of_term : term -> string

val string_of_formula : formula -> string
