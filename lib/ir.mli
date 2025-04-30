module Map = Base.Map.Poly

type varname = string
type predname = varname

type atom =
  | Var of predname
  | Pow2 of predname
[@@deriving variants]

type mul = Mul of int * atom [@@deriving variants]
type term = Sum of (atom, int) Map.t [@@deriving variants]

type formula =
  | True
  | False
  | Pred of predname * Ast.term list
  | Eq of term * int
  | Leq of term * int
  | Mnot of formula
  | Mand of formula * formula
  | Mor of formula * formula
  | Mimpl of formula * formula
  | Miff of formula * formula
  | Exists of predname list * formula
  | Any of predname list * formula
[@@deriving variants]

val inverse : term -> term
val add : term -> term -> term
val collect_term : Ast.term -> term * int
val binary_minus : term -> term -> term
val formula_of_ast : Ast.formula -> formula
