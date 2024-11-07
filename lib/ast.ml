(** Copyright 2024, MacadamiaSolver. *)

(** SPDX-License-Identifier: MIT *)

type varname = string

type predname = string

type term =
  | Var of varname
  | Const of int
  | Add of term * term
  | Mul of int * term
  | Pow of int * term

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
  | Pow2 of term

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

let pow x y = Pow (x, y)

let pred n p = Pred (n, p)

let mtrue () = True

let mfalse () = False

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
  | Var n ->
      Format.fprintf ppf "%s" n
  | Const n ->
      Format.fprintf ppf "%d" n
  | Add (a, b) ->
      Format.fprintf ppf "(%a + %a)" pp_term a pp_term b
  | Mul (a, b) ->
      Format.fprintf ppf "(%d * %a)" a pp_term b
  | Pow (a, b) ->
      Format.fprintf ppf "(%d ** %a)" a pp_term b

let rec pp_formula ppf = function
  | True ->
      Format.fprintf ppf "True"
  | False ->
      Format.fprintf ppf "False"
  | Pred (a, b) ->
      Format.fprintf ppf "(P %s %a)" a (Format.pp_print_list pp_term) b
  | Eq (a, b) ->
      Format.fprintf ppf "(%a = %a)" pp_term a pp_term b
  | Neq (a, b) ->
      Format.fprintf ppf "(%a != %a)" pp_term a pp_term b
  | Lt (a, b) ->
      Format.fprintf ppf "(%a < %a)" pp_term a pp_term b
  | Gt (a, b) ->
      Format.fprintf ppf "(%a > %a)" pp_term a pp_term b
  | Leq (a, b) ->
      Format.fprintf ppf "(%a <= %a)" pp_term a pp_term b
  | Geq (a, b) ->
      Format.fprintf ppf "(%a >= %a)" pp_term a pp_term b
  | Mnot a ->
      Format.fprintf ppf "(~ %a)" pp_formula a
  | Mand (a, b) ->
      Format.fprintf ppf "(%a & %a)" pp_formula a pp_formula b
  | Mor (a, b) ->
      Format.fprintf ppf "(%a | %a)" pp_formula a pp_formula b
  | Mimpl (a, b) ->
      Format.fprintf ppf "(%a -> %a)" pp_formula a pp_formula b
  | Miff (a, b) ->
      Format.fprintf ppf "(%a <-> %a)" pp_formula a pp_formula b
  | Exists (a, b) ->
      Format.fprintf ppf "(E%a %a)"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
           Format.pp_print_string )
        a pp_formula b
  | Any (a, b) ->
      Format.fprintf ppf "(A%a %a)"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
           Format.pp_print_string )
        a pp_formula b
  | Pow2 a ->
      Format.fprintf ppf "(Pow2 %a)" pp_term a

let quantifier_ast_exn = function
  | Exists _ ->
      exists
  | Any _ ->
      any
  | _ ->
      assert false

let binconj_ast_exn = function
  | Mand _ ->
      mand
  | Mor _ ->
      mor
  | Mimpl _ ->
      mimpl
  | Miff _ ->
      miff
  | _ ->
      assert false

let fold ff ft acc f =
  let rec foldt acc = function
    | (Const _ | Var _) as f ->
        ft acc f
    | (Pow (_, t1) | Mul (_, t1)) as t ->
        ft (foldt acc t1) t
    | Add (t1, t2) as t ->
        ft (foldt (foldt acc t1) t2) t
  in
  let rec foldf acc = function
    | (True | False) as f ->
        ff acc f
    | ( Eq (t1, t2)
      | Lt (t1, t2)
      | Gt (t1, t2)
      | Leq (t1, t2)
      | Geq (t1, t2)
      | Neq (t1, t2) ) as f ->
        ff (foldt (foldt acc t1) t2) f
    | (Mor (f1, f2) | Mand (f1, f2) | Miff (f1, f2) | Mimpl (f1, f2)) as f ->
        ff (foldf (foldf acc f1) f2) f
    | Mnot f1 as f ->
        ff (foldf acc f1) f
    | (Exists (_, f1) | Any (_, f1)) as f ->
        ff (foldf acc f1) f
    | Pred (_, _) as f ->
        ff acc f
    | _ ->
        failwith "Unimplemented"
  in
  foldf acc f

let for_some ff ft f =
  fold
    (fun acc f -> ff f |> ( || ) acc)
    (fun acc t -> ft t |> ( || ) acc)
    false f

let for_all ff ft f =
  fold
    (fun acc f -> ff f |> ( && ) acc)
    (fun acc t -> ft t |> ( && ) acc)
    true f

let map ff ft f =
  let rec mapt = function
    | (Const _ | Var _) as f ->
        ft f
    | Mul (a, t1) ->
        Mul (a, mapt t1) |> ft
    | Add (t1, t2) ->
        Add (mapt t1, mapt t2) |> ft
    | Pow (a, t1) ->
        Pow (a, mapt t1) |> ft
  in
  let rec mapf = function
    | (True | False) as f ->
        f |> ff
    | Eq (t1, t2) ->
        Eq (mapt t1, mapt t2) |> ff
    | Lt (t1, t2) ->
        Lt (mapt t1, mapt t2) |> ff
    | Gt (t1, t2) ->
        Gt (mapt t1, mapt t2) |> ff
    | Leq (t1, t2) ->
        Leq (mapt t1, mapt t2) |> ff
    | Geq (t1, t2) ->
        Geq (mapt t1, mapt t2) |> ff
    | Neq (t1, t2) ->
        Neq (mapt t1, mapt t2) |> ff
    | Mor (f1, f2) ->
        Mor (mapf f1, mapf f2) |> ff
    | Mand (f1, f2) ->
        Mand (mapf f1, mapf f2) |> ff
    | Miff (f1, f2) ->
        Miff (mapf f1, mapf f2) |> ff
    | Mimpl (f1, f2) ->
        Mimpl (mapf f1, mapf f2) |> ff
    | Mnot f1 ->
        Mnot (mapf f1) |> ff
    | Exists (a, f1) ->
        Exists (a, mapf f1) |> ff
    | Any (a, f1) ->
        Any (a, mapf f1) |> ff
    | Pred (_, _) as f ->
        f |> ff
    | _ ->
        failwith "Unimplemented"
  in
  mapf f
