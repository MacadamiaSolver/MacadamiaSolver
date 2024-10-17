open Lib
module Parser = Smtlib_utils.V_2_6
module Ast = Parser.Ast
module Formula = Lib.Ast

type state =
  { asserts: Formula.formula list
  ; vars: string list
  ; status: bool option
  ; sat: bool option }

let init = {asserts= []; vars= []; status= None; sat= None}

let add_assertion assertion ({asserts; _} as state) =
  {state with asserts= assertion :: asserts}

let add_var var ({vars; _} as state) = {state with vars= var :: vars}

let run {asserts; vars; _} =
  match asserts with
    | h :: tl ->
        List.fold_left Formula.mand h tl
        |> (fun f -> List.fold_left (Fun.flip Formula.exists) f vars)
        |> Solver.proof |> Result.get_ok
    | [] ->
        true

let term_of_binop = function
  | Ast.Add ->
      Formula.add
  | Ast.Mult -> (
      function
      | Formula.Const const ->
          Formula.mul const
      | _ ->
          failwith "Invalid multipliaction" )
  | _ ->
      failwith "Invalid binop for terms"

let rec term_of_smtlib = function
  | Ast.Const const ->
      const |> int_of_string_opt |> Option.map Formula.const
      |> Base.Option.value ~default:(Formula.var const)
  | Ast.Arith (op, h :: tl) ->
      tl |> List.map term_of_smtlib
      |> List.fold_left (term_of_binop op) (term_of_smtlib h)
  | _ ->
      failwith "Unimplemented term"

let formula_of_binop = function
  | Ast.Leq ->
      Formula.leq
  | Ast.Lt ->
      Formula.lt
  | Ast.Geq ->
      Formula.geq
  | Ast.Gt ->
      Formula.gt
  | _ ->
      failwith "Invalid binop for formulas"

let rec formula_of_smtlib = function
  | Ast.Arith (op, [lhs; rhs]) ->
      (formula_of_binop op) (term_of_smtlib lhs) (term_of_smtlib rhs)
  | Ast.Eq (a, b) ->
      Formula.Eq (term_of_smtlib a, term_of_smtlib b)
  | Ast.Imply (a, b) ->
      Formula.Mimpl (formula_of_smtlib a, formula_of_smtlib b)
  | Ast.And (h :: tl) ->
      tl |> List.map formula_of_smtlib
      |> List.fold_left Formula.mand (formula_of_smtlib h)
  | Ast.Or (h :: tl) ->
      tl |> List.map formula_of_smtlib
      |> List.fold_left Formula.mor (formula_of_smtlib h)
  | Ast.Not t ->
      t |> formula_of_smtlib |> Formula.mnot
  | Ast.Forall (vs, f) ->
      if vs |> List.map snd |> List.exists (( <> ) (Ast.Ty_app ("Int", [])))
      then failwith "Only integer type supported"
      else
        vs |> List.map fst
        |> List.fold_left (Fun.flip Formula.any) (formula_of_smtlib f)
  | Ast.Exists (vs, f) ->
      if vs |> List.map snd |> List.exists (( <> ) (Ast.Ty_app ("Int", [])))
      then failwith "Only integer type supported"
      else
        vs |> List.map fst
        |> List.fold_left (Fun.flip Formula.exists) (formula_of_smtlib f)
  | Ast.Let (vs, f) ->
      let f =
        vs
        |> List.map (fun (v, t) -> Formula.Eq (Formula.Var v, term_of_smtlib t))
        |> List.fold_left Formula.mand (formula_of_smtlib f)
      in
      vs |> List.map fst |> List.fold_left (Fun.flip Formula.exists) f
  | _ ->
      failwith "Unimplemented formula"

let sat_of_bool = function true -> "sat" | false -> "unsat"

let bool_of_sat_fail = function
  | "unsat" ->
      false
  | "sat" ->
      true
  | _ ->
      failwith "Unknown sat status"

let exec ({sat; status; _} as state) = function
  | Ast.Stmt_set_logic logic ->
      if String.ends_with ~suffix:"LIA" logic then state
      else failwith "Only LIA logic is supported"
  | Ast.Stmt_set_info (k, v) ->
      if k = ":status" then
        let sat = bool_of_sat_fail v in
        {state with sat= Some sat}
      else state
  | Ast.Stmt_decl decl ->
      if
        decl.fun_args <> [] || decl.fun_ty_vars <> []
        || decl.fun_ret <> Ast.Ty_app ("Int", [])
      then
        failwith
          "Only decls of integer functions with no arguments are supported"
      else state |> add_var decl.fun_name
  | Ast.Stmt_check_sat ->
      let status = run state in
      Format.printf "%s\n" (sat_of_bool status);
      sat
      |> Option.iter (fun sat ->
             if sat <> status then
               Format.printf "Error: check annotations says %s\n"
                 (sat_of_bool sat)
             else () );
      {state with status= Some status}
  | Ast.Stmt_exit ->
      exit (if sat = status then 0 else 1)
  | Ast.Stmt_assert term ->
      state |> add_assertion (formula_of_smtlib term)
  | _ ->
      failwith "Unimplemented statement"

let () =
  let filename = Array.get Sys.argv 1 in
  let ast = Parser.parse_file_exn filename |> List.map Ast.view in
  List.fold_left exec init ast |> ignore
