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

let var x = Var x

let const x = Const x

let add x y = Add (x, y)

let equals x y = Equals (x, y)

let mnot x = Mnot x

let mand x y = Mand (x, y)

let mor x y = Mor (x, y)

let mimpl x y = Mimpl (x, y)

let exists x y = Exists (x, y)

let any x y = Any (x, y)

let rec string_of_term = function
  | Var n ->
      "(Var " ^ n ^ ")"
  | Const n ->
      "(Const " ^ string_of_int n ^ ")"
  | Add (a, b) ->
      "(Add " ^ string_of_term a ^ " " ^ string_of_term b ^ ")"

let rec string_of_formula = function
  | Equals (a, b) ->
      "(Equals " ^ string_of_term a ^ " " ^ string_of_term b ^ ")"
  | Mnot a ->
      "(Not " ^ string_of_formula a ^ ")"
  | Mand (a, b) ->
      "(And " ^ string_of_formula a ^ " " ^ string_of_formula b ^ ")"
  | Mor (a, b) ->
      "(Or " ^ string_of_formula a ^ " " ^ string_of_formula b ^ ")"
  | Mimpl (a, b) ->
      "(Impl " ^ string_of_formula a ^ " " ^ string_of_formula b ^ ")"
  | Exists (x, a) ->
      "(Exists " ^ x ^ " " ^ string_of_formula a ^ ")"
  | Any (x, a) ->
      "(Any " ^ x ^ " " ^ string_of_formula a ^ ")"
