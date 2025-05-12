module Map = Base.Map.Poly

(* TODO: the perfect implementation should differentiate between atoms in *)
(* different theories. But it requires a lot more complex parsing due to *)
(* the state that should be stored. So let's stick with simpler stuff now. *)
type atom =
  | Var of string
  | Internal of string
  | Pow2 of string
[@@deriving variants]

let internal () = internal (Random.int (Int.max_int / 2) |> string_of_int)

let pp_atom fmt = function
  | Var var -> Format.fprintf fmt "%s" var
  | Internal var -> Format.fprintf fmt "[%s]" var
  | Pow2 var -> Format.fprintf fmt "pow2(%s)" var
;;

(** Exponential integer arithmetic, i.e. LIA with exponents.*)
module Eia = struct
  type t = Sum of (atom, int) Map.t [@@deriving variants]

  let pp fmt = function
    | Sum term ->
      Format.fprintf
        fmt
        "%a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt " + ")
           (fun fmt (a, b) -> Format.fprintf fmt "%d%a" b pp_atom a))
        (Map.to_alist term)
  ;;

  type ir =
    | Eq of t * int
    | Lt of
        t * int (* TODO: this might be simplified when negative integers will be added. *)
    | Leq of t * int
    | Gt of t * int
    | Geq of t * int
  [@@deriving variants, show]

  let map_ir f = function
    | Eq (term, c) ->
      (match f term c with
       | term, c -> Eq (term, c))
    | Leq (term, c) ->
      (match f term c with
       | term, c -> Leq (term, c))
  ;;

  let pp_ir fmt = function
    | Eq (term, c) -> Format.fprintf fmt "%a = %d" pp term c
    | Leq (term, c) -> Format.fprintf fmt "%a <= %d" pp term c
    | Lt (term, c) -> Format.fprintf fmt "%a <= %d" pp term c
    | Geq (term, c) -> Format.fprintf fmt "%a >= %d" pp term c
    | Gt (term, c) -> Format.fprintf fmt "%a > %d" pp term c
  ;;

  let equal formula formula' =
    match formula, formula' with
    | Eq (Sum term, c), Eq (Sum term', c')
    | Leq (Sum term, c), Leq (Sum term', c')
    | Geq (Sum term, c), Geq (Sum term', c')
    | Lt (Sum term, c), Lt (Sum term', c')
    | Gt (Sum term, c), Gt (Sum term', c') -> Map.equal ( = ) term term' && c = c'
    | _, _ -> false
  ;;
end

(** Bitvectors. *)
module Bv = struct
  type t =
    | Const of Bitv.t
    | Atom of atom
    | And of t list
    | Or of t list
    | Xor of t * t
    | Neg of t
  [@@deriving variants]

  let rec pp fmt = function
    | Const bv -> Format.fprintf fmt "%a" Bitv.L.print bv
    | Atom atom -> Format.fprintf fmt "%a" pp_atom atom
    | And terms ->
      Format.fprintf
        fmt
        "(%a)"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " & ") pp)
        terms
    | Or terms ->
      Format.fprintf
        fmt
        "(%a)"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ") pp)
        terms
    | Xor (a, b) -> Format.fprintf fmt "%a ^ %a" pp a pp b
    | Neg term -> Format.fprintf fmt "~%a" pp term
  ;;

  type ir =
    | Eq of t list
    | Leq of t * t
    | Geq of t * t
    | Gt of t * t
    | Lt of t * t
  [@@deriving variants]

  let pp_ir fmt = function
    | Eq terms ->
      Format.fprintf
        fmt
        "(%a)"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " = ") pp)
        terms
    | Leq (a, b) -> Format.fprintf fmt "%a <= %a" pp a pp b
    | Lt (a, b) -> Format.fprintf fmt "%a <= %a" pp a pp b
    | Geq (a, b) -> Format.fprintf fmt "%a >= %a" pp a pp b
    | Gt (a, b) -> Format.fprintf fmt "%a > %a" pp a pp b
  ;;

  let equal = ( = )
end

type t =
  | True
  (* Theories. *)
  | Eia of Eia.ir
  | Bv of Bv.ir
  (* Logical operations. *)
  | Lnot of t
  | Land of t list
  | Lor of t list
  | Exists of atom list * t
  | Pred of string * Eia.t list
[@@deriving variants]

let rec pp fmt = function
  | True -> Format.fprintf fmt "true"
  | Eia ir -> Format.fprintf fmt "%a" Eia.pp_ir ir
  | Bv ir -> Format.fprintf fmt "%a" Bv.pp_ir ir
  | Lnot ir -> Format.fprintf fmt "~%a" pp ir
  | Land irs ->
    Format.fprintf
      fmt
      "(%a)"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " & ") pp)
      irs
  | Lor irs ->
    Format.fprintf
      fmt
      "(%a)"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ") pp)
      irs
  | Exists (atoms, ir) ->
    Format.fprintf
      fmt
      "(exists (%a) %a)"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_atom)
      atoms
      pp
      ir
  | Pred (name, args) ->
    Format.fprintf
      fmt
      "%s(%a)"
      name
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") Eia.pp)
      args
;;

(* Structural equivalence of the IR formulas. *)
let rec equal ir ir' =
  match ir, ir' with
  | True, True -> true
  | Eia eia_ir, Eia eia_ir' -> Eia.equal eia_ir eia_ir'
  | Bv bv_ir, Bv bv_ir' -> Bv.equal bv_ir bv_ir'
  | Lnot ir, Lnot ir' -> equal ir ir'
  | Land irs, Land irs' | Lor irs, Lor irs' -> List.for_all2 equal irs irs'
  | Exists (atoms, ir), Exists (atoms', ir') ->
    List.equal ( = ) atoms atoms' && equal ir ir'
  | _, _ -> false
;;

let rec map f ir =
  match ir with
  | True | Eia _ | Bv _ | Pred _ -> f ir
  | Lnot ir' -> f (lnot (map f ir'))
  | Land irs -> f (land_ (List.map (map f) irs))
  | Lor irs -> f (lor_ (List.map (map f) irs))
  | Exists (atoms, ir') -> f (exists atoms (map f ir'))
;;

let rec fold f acc ir =
  match ir with
  | True | Eia _ | Bv _ | Pred (_, _) -> f acc ir
  | Lnot ir' -> f (fold f acc ir') ir
  | Land irs -> f (List.fold_left (fold f) acc irs) ir
  | Lor irs -> f (List.fold_left (fold f) acc irs) ir
  | Exists (_, ir') -> f (fold f acc ir') ir
;;

let for_all f ir = fold (fun acc ir -> f ir |> ( && ) acc) true ir
let for_some f ir = fold (fun acc ir -> f ir |> ( || ) acc) false ir
