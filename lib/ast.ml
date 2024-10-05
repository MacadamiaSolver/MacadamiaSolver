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

let var x = Var x

let const x = Const x

let add x y = Add (x, y)

let mul x y = Mul (x, y)

let pred n p = Pred (n, p)

let equals x y = Equals (x, y)

let mnot x = Mnot x

let mand x y = Mand (x, y)

let mor x y = Mor (x, y)

let mimpl x y = Mimpl (x, y)

let exists x y = Exists (x, y)

let any x y = Any (x, y)

let def x p f = Def (x, p, f)

let eval f = Eval f

let dump f = Dump f

let rec string_of_term = function
  | Var n ->
      "(Var " ^ n ^ ")"
  | Const n ->
      "(Const " ^ string_of_int n ^ ")"
  | Add (a, b) ->
      "(Add " ^ string_of_term a ^ " " ^ string_of_term b ^ ")"
  | Mul (a, b) ->
      "(Mul " ^ string_of_int a ^ " " ^ string_of_term b ^ ")"

let rec string_of_formula = function
  | Pred (a, b) ->
      "(Pred " ^ a ^ " " ^ String.concat " " (List.map string_of_term b) ^ ")"
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

let string_of_stmt = function
  | Eval f ->
      "Eval " ^ string_of_formula f
  | Dump f ->
      "Dump " ^ string_of_formula f
  | Def (x, p, f) ->
      "Def " ^ x ^ " " ^ String.concat " " p ^ " = " ^ string_of_formula f
