(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

type varpos = int

module type Type = sig
  type t

  val add : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val eq : varpos -> varpos -> t
  val eq_const : varpos -> int -> t
  val n : unit -> t
  val z : unit -> t
  val leq : varpos -> varpos -> t
  val geq : varpos -> varpos -> t
  val lt : varpos -> varpos -> t
  val gt : varpos -> varpos -> t
  val power_of_two : int -> t
  val bvor : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val bvand : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val bvxor : lhs:varpos -> rhs:varpos -> res:varpos -> t
end

module Lsb : sig
  include Type with type t := Nfa.Lsb.t

  val neq : varpos -> varpos -> Nfa.Lsb.t
  val torename : varpos -> int -> int -> Nfa.Lsb.t
  val torename2 : int -> int -> Nfa.Lsb.t
  val mul : res:varpos -> lhs:int -> rhs:varpos -> Nfa.Lsb.t
end

module Msb : sig
  include Type with type t := Nfa.Msb.t

  val minus : varpos -> varpos -> Nfa.Msb.t
  val geq_zero : varpos -> Nfa.Msb.t
end

module MsbNat : sig
  val add : lhs:varpos -> rhs:varpos -> res:varpos -> Nfa.MsbNat.t
  val eq : varpos -> varpos -> Nfa.MsbNat.t
  val eq_const : varpos -> int -> Nfa.MsbNat.t
  val geq : varpos -> varpos ->  Nfa.MsbNat.t
  val mul : res:varpos -> lhs:int -> rhs:varpos -> Nfa.MsbNat.t
  val torename : varpos -> int -> int -> Nfa.MsbNat.t
  val torename2 : int -> int -> Nfa.MsbNat.t
end
