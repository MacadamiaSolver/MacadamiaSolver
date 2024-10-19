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

val var : varname -> term

val const : int -> term

val add : term -> term -> term

val mul : int -> term -> term

val pred : predname -> term list -> formula

val eq : term -> term -> formula

val neq : term -> term -> formula

val lt : term -> term -> formula

val gt : term -> term -> formula

val leq : term -> term -> formula

val geq : term -> term -> formula

val mnot : formula -> formula

val mand : formula -> formula -> formula

val mor : formula -> formula -> formula

val mimpl : formula -> formula -> formula

val miff : formula -> formula -> formula

val exists : varname -> formula -> formula

val any : varname -> formula -> formula

val def : string -> varname list -> formula -> stmt

val eval : formula -> stmt

val dump : formula -> stmt

val parse : formula -> stmt

val list : unit -> stmt

val help : unit -> stmt

val pp_term : Format.formatter -> term -> unit

val pp_formula : Format.formatter -> formula -> unit
