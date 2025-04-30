module Map = Base.Map.Poly

type varname = string
type predname = string

type atom =
  | Var of varname
  | Pow2 of varname
[@@deriving variants]

type mul = Mul of int * atom [@@deriving variants]
type term = Sum of (atom, int) Map.t [@@deriving variants]

type formula =
  | True
  | False
  | Pred of predname * Ast.term list (* TODO *)
  | Eq of term * int
  | Leq of term * int
  | Mnot of formula
  | Mand of formula * formula
  | Mor of formula * formula
  | Mimpl of formula * formula
  | Miff of formula * formula
  | Exists of varname list * formula
  | Any of varname list * formula
[@@deriving variants]

let inverse (Sum term) = Sum (Map.map ~f:( ~- ) term)

let add (Sum lhs) (Sum rhs) =
  Map.fold2 lhs rhs ~init:Map.empty ~f:(fun ~key ~data acc ->
    let data =
      match data with
      | `Right data -> data
      | `Left data -> data
      | `Both (l, r) -> l + r
    in
    Map.add_exn acc ~key ~data)
  |> sum
;;

let rec collect_term = function
  | Ast.Var x -> Sum (Map.singleton (Var x) 1), 0
  | Ast.Const c -> Sum Map.empty, c
  | Ast.Add (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    add lt rt, lc + rc
  | Ast.Mul (lhs, rhs) ->
    let Sum term, c = collect_term rhs in
    Sum (Map.map term ~f:(( * ) lhs)), lhs * c
  | Ast.Pow (base, exp) ->
    if base <> 2
    then failwith "Only base 2 is supported"
    else (
      match exp with
      | Var exp -> Sum (Map.singleton (Pow2 exp) 1), 0
      | _ -> failwith "TODO: Only variables in exponents are currently supported")
;;

let binary_minus lhs rhs = add lhs (inverse rhs)

let rec formula_of_ast = function
  | Ast.True -> True
  | Ast.False -> False
  | Ast.Pred (p, l) -> Pred (p, l)
  | Ast.Eq (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Eq (binary_minus lt rt, rc - lc)
  | Ast.Neq (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Mnot (Eq (binary_minus lt rt, rc - lc))
  | Ast.Leq (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Leq (binary_minus lt rt, rc - lc)
  | Ast.Geq (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Leq (binary_minus rt lt, lc - rc)
  | Ast.Lt (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Leq (binary_minus lt rt, rc - lc - 1)
  | Ast.Gt (lhs, rhs) ->
    let lt, lc = collect_term lhs in
    let rt, rc = collect_term rhs in
    Leq (binary_minus rt lt, lc - rc + 1)
  | Ast.Mnot _ -> failwith ""
  | Ast.Mand (lhs, rhs) -> Mand (formula_of_ast lhs, formula_of_ast rhs)
  | Ast.Mor (lhs, rhs) -> Mor (formula_of_ast lhs, formula_of_ast rhs)
  | Ast.Mimpl (lhs, rhs) -> Mimpl (formula_of_ast lhs, formula_of_ast rhs)
  | Ast.Miff (lhs, rhs) -> Miff (formula_of_ast lhs, formula_of_ast rhs)
  | Ast.Exists (vars, formula) -> Exists (vars, formula_of_ast formula)
  | Ast.Any (vars, formula) -> Any (vars, formula_of_ast formula)
;;
