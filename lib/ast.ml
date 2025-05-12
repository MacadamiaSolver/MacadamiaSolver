(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

type varname = string
type predname = string

type term =
  | Var of varname
  | Const of int
  | Add of term * term
  | Mul of int * term
  | Bvand of term * term
  | Bvor of term * term
  | Bvxor of term * term
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

let rec pp_term ppf = function
  | Var n -> Format.fprintf ppf "%s" n
  | Const n -> Format.fprintf ppf "%d" n
  | Add (a, b) -> Format.fprintf ppf "(%a + %a)" pp_term a pp_term b
  | Bvor (a, b) -> Format.fprintf ppf "(%a | %a)" pp_term a pp_term b
  | Bvxor (a, b) -> Format.fprintf ppf "(%a ^ %a)" pp_term a pp_term b
  | Bvand (a, b) -> Format.fprintf ppf "(%a & %a)" pp_term a pp_term b
  | Mul (a, b) -> Format.fprintf ppf "(%d * %a)" a pp_term b
  | Pow (a, b) -> Format.fprintf ppf "(%d ** %a)" a pp_term b
;;

let rec pp_formula ppf = function
  | True -> Format.fprintf ppf "True"
  | False -> Format.fprintf ppf "False"
  | Pred (a, b) -> Format.fprintf ppf "(P %s %a)" a (Format.pp_print_list pp_term) b
  | Eq (a, b) -> Format.fprintf ppf "(%a = %a)" pp_term a pp_term b
  | Neq (a, b) -> Format.fprintf ppf "(%a != %a)" pp_term a pp_term b
  | Lt (a, b) -> Format.fprintf ppf "(%a < %a)" pp_term a pp_term b
  | Gt (a, b) -> Format.fprintf ppf "(%a > %a)" pp_term a pp_term b
  | Leq (a, b) -> Format.fprintf ppf "(%a <= %a)" pp_term a pp_term b
  | Geq (a, b) -> Format.fprintf ppf "(%a >= %a)" pp_term a pp_term b
  | Mnot a -> Format.fprintf ppf "(~ %a)" pp_formula a
  | Mand (a, b) -> Format.fprintf ppf "(%a & %a)" pp_formula a pp_formula b
  | Mor (a, b) -> Format.fprintf ppf "(%a | %a)" pp_formula a pp_formula b
  | Mimpl (a, b) -> Format.fprintf ppf "(%a -> %a)" pp_formula a pp_formula b
  | Miff (a, b) -> Format.fprintf ppf "(%a <-> %a)" pp_formula a pp_formula b
  | Exists (a, b) ->
    Format.fprintf
      ppf
      "(E%a %a)"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         Format.pp_print_string)
      a
      pp_formula
      b
  | Any (a, b) ->
    Format.fprintf
      ppf
      "(A%a %a)"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         Format.pp_print_string)
      a
      pp_formula
      b
;;

let quantifier_ast_exn = function
  | Exists _ -> exists
  | Any _ -> any
  | _ -> assert false
;;

let binconj_ast_exn = function
  | Mand _ -> mand
  | Mor _ -> mor
  | Mimpl _ -> mimpl
  | Miff _ -> miff
  | _ -> assert false
;;

let tfold ft acc t =
  let rec foldt acc = function
    | (Const _ | Var _) as f -> ft acc f
    | (Pow (_, t1) | Mul (_, t1)) as t -> ft (foldt acc t1) t
    | (Add (t1, t2) | Bvand (t1, t2) | Bvor (t1, t2) | Bvxor (t1, t2)) as t ->
      ft (foldt (foldt acc t1) t2) t
  in
  foldt acc t
;;

let fold ff ft acc f =
  let rec foldt acc = function
    | (Const _ | Var _) as f -> ft acc f
    | (Pow (_, t1) | Mul (_, t1)) as t -> ft (foldt acc t1) t
    | (Add (t1, t2) | Bvand (t1, t2) | Bvor (t1, t2) | Bvxor (t1, t2)) as t ->
      ft (foldt (foldt acc t1) t2) t
  in
  let rec foldf acc = function
    | (True | False) as f -> ff acc f
    | ( Eq (t1, t2)
      | Lt (t1, t2)
      | Gt (t1, t2)
      | Leq (t1, t2)
      | Geq (t1, t2)
      | Neq (t1, t2) ) as f -> ff (foldt (foldt acc t1) t2) f
    | (Mor (f1, f2) | Mand (f1, f2) | Miff (f1, f2) | Mimpl (f1, f2)) as f ->
      ff (foldf (foldf acc f1) f2) f
    | Mnot f1 as f -> ff (foldf acc f1) f
    | (Exists (_, f1) | Any (_, f1)) as f -> ff (foldf acc f1) f
    | Pred (_, args) as f -> ff (List.fold_left foldt acc args) f
  in
  foldf acc f
;;

let for_some ff ft f =
  fold (fun acc f -> ff f |> ( || ) acc) (fun acc t -> ft t |> ( || ) acc) false f
;;

let for_all ff ft f =
  fold (fun acc f -> ff f |> ( && ) acc) (fun acc t -> ft t |> ( && ) acc) true f
;;

let map ff ft f =
  let rec mapt = function
    | (Const _ | Var _) as f -> ft f
    | Mul (a, t1) -> Mul (a, mapt t1) |> ft
    | Add (t1, t2) -> Add (mapt t1, mapt t2) |> ft
    | Bvand (t1, t2) -> Bvand (mapt t1, mapt t2) |> ft
    | Bvor (t1, t2) -> Bvor (mapt t1, mapt t2) |> ft
    | Bvxor (t1, t2) -> Bvxor (mapt t1, mapt t2) |> ft
    | Pow (a, t1) -> Pow (a, mapt t1) |> ft
  in
  let rec mapf = function
    | (True | False) as f -> f |> ff
    | Eq (t1, t2) -> Eq (mapt t1, mapt t2) |> ff
    | Lt (t1, t2) -> Lt (mapt t1, mapt t2) |> ff
    | Gt (t1, t2) -> Gt (mapt t1, mapt t2) |> ff
    | Leq (t1, t2) -> Leq (mapt t1, mapt t2) |> ff
    | Geq (t1, t2) -> Geq (mapt t1, mapt t2) |> ff
    | Neq (t1, t2) -> Neq (mapt t1, mapt t2) |> ff
    | Mor (f1, f2) -> Mor (mapf f1, mapf f2) |> ff
    | Mand (f1, f2) -> Mand (mapf f1, mapf f2) |> ff
    | Miff (f1, f2) -> Miff (mapf f1, mapf f2) |> ff
    | Mimpl (f1, f2) -> Mimpl (mapf f1, mapf f2) |> ff
    | Mnot f1 -> Mnot (mapf f1) |> ff
    | Exists (a, f1) -> Exists (a, mapf f1) |> ff
    | Any (a, f1) -> Any (a, mapf f1) |> ff
    | Pred (_, _) as f -> f |> ff
  in
  mapf f
;;
