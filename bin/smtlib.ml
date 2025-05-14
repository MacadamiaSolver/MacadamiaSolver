module Map = Base.Map.Poly

module Conv = struct
  open Lib
  open Smtml

  let rec _to_ir orig_expr =
    let expect_eia expr =
      match expr |> _to_ir with
      | `Eia (Ir.Eia.Sum term, c) -> term, c
      | `Symbol var -> Map.singleton (Ir.var var) 1, 0
      | _ -> failwith "Expected EIA term"
    in
    let expect_ir expr =
      match expr |> _to_ir with
      | `Ir ir -> ir
      | `Symbol ir -> Ir.pred ir []
      | _ -> failwith "Expected boolean term"
    in
    (* Format.printf "%a\n%!" Expr.pp orig_expr; *)
    let expr = Expr.view orig_expr in
    match expr with
    (* Constants. *)
    | Expr.Val v -> begin
      match v with
      | True -> `Ir Ir.true_
      | Int d -> `Eia (Ir.Eia.sum Map.empty, d)
      | _ -> failwith "err"
    end
    (* Variables. *)
    | Expr.Symbol symbol ->
      let var = Symbol.to_string symbol in
      `Symbol var
    (* Yes, probably this stuff is kinda over-engineered. *)
    | Expr.App (symbol, [ expr ])
      when match Expr.view expr with
           | Symbol { name = Symbol.Simple "Int"; _ } -> true
           | _ -> false ->
      let var = Symbol.to_string symbol in
      `Symbol var
    (* Semenov arithmetic, i.e. 2**x operators. *)
    | Expr.App ({ name = Symbol.Simple "pow2"; _ }, [ expr ]) ->
      let atom =
        match expr |> _to_ir with
        | `Symbol symbol -> symbol
        | _ -> failwith "Semenov now only supports vars as an exponent"
      in
      `Eia (Ir.Eia.sum (Map.singleton (Ir.pow2 atom) 1), 0)
    | Expr.App ({ name = Symbol.Simple "exp"; _ }, [ base; expr ])
      when base = Expr.value (Value.Int 2) ->
      let atom =
        match expr |> _to_ir with
        | `Symbol symbol -> symbol
        | _ -> failwith "Semenov now only supports vars as an exponent"
      in
      `Eia (Ir.Eia.sum (Map.singleton (Ir.pow2 atom) 1), 0)
    (* Arithmetic operations. *)
    | Expr.Unop (_ty, Ty.Unop.Neg, expr) -> begin
      match expr |> _to_ir with
      | `Eia (Ir.Eia.Sum atoms, c) ->
        let term = atoms |> Map.map ~f:(fun a -> -a) |> Ir.Eia.sum in
        let c = -c in
        `Eia (term, c)
      | _ -> failwith "Unimplemented "
    end
    | Expr.Binop (_ty, Ty.Binop.Mul, lhs, rhs) -> begin
      let lhs_term, lhs_c = expect_eia lhs in
      let rhs_term, rhs_c = expect_eia rhs in
      if Map.is_empty lhs_term || Map.is_empty rhs_term
      then (
        let atoms, multiplier =
          if Map.is_empty rhs_term then lhs_term, rhs_c else rhs_term, lhs_c
        in
        let atoms = atoms |> Map.map ~f:(fun a -> a * multiplier) in
        let c = lhs_c * rhs_c in
        `Eia (Ir.Eia.sum atoms, c))
      else failwith "Only multiplying by constant is supported"
    end
    | Expr.Binop (_ty, Ty.Binop.Add, lhs, rhs) -> begin
      let lhs_term, lhs_c = expect_eia lhs in
      let rhs_term, rhs_c = expect_eia rhs in
      let term =
        Map.merge lhs_term rhs_term ~f:(fun ~key:_ vs ->
          match vs with
          | `Left a | `Right a -> Some a
          | `Both (a, b) -> Some (a + b))
      in
      let c = lhs_c + rhs_c in
      `Eia (Ir.Eia.sum term, c)
    end
    | Expr.Binop (_ty, Ty.Binop.Sub, lhs, rhs) ->
      let lhs_term, lhs_c = expect_eia lhs in
      let rhs_term, rhs_c = expect_eia rhs in
      let atoms =
        Map.merge lhs_term rhs_term ~f:(fun ~key:_ vs ->
          match vs with
          | `Left a -> Some a
          | `Right a -> Some (-a)
          | `Both (a, b) -> Some (a - b))
      in
      let c = lhs_c - rhs_c in
      `Eia (Ir.Eia.Sum atoms, c)
    (* Logical operations. *)
    (* Not. *)
    | Expr.Unop (_ty, Ty.Unop.Not, expr) -> begin
      match expr |> _to_ir with
      | `Ir expr -> `Ir (Ir.lnot expr)
      | `Symbol pred -> `Ir (Ir.lnot (Ir.pred pred []))
      | _ -> failwith "Couldn't convert the statement within not to the supported one"
    end
    (* Binary and arbitrary and *)
    | Expr.Binop (_ty, Ty.Binop.And, lhs, rhs) ->
      `Ir (Ir.land_ [ expect_ir lhs; expect_ir rhs ])
    | Expr.Naryop (_ty, Ty.Naryop.Logand, exprs) ->
      let exprs = List.map expect_ir exprs in
      `Ir (Ir.land_ exprs)
    (* Binary and arbitrary or *)
    | Expr.Binop (_ty, Ty.Binop.Or, lhs, rhs) -> begin
      `Ir (Ir.lor_ [ expect_ir lhs; expect_ir rhs ])
    end
    | Expr.Naryop (_ty, Ty.Naryop.Logor, exprs) ->
      let exprs = List.map expect_ir exprs in
      `Ir (Ir.lor_ exprs)
    (* Implication *)
    | Expr.Binop (_ty, Ty.Binop.Implies, lhs, rhs) -> begin
      match lhs |> _to_ir, rhs |> _to_ir with
      | `Ir lhs, `Ir rhs -> `Ir (Ir.lor_ [ Ir.lnot lhs; rhs ])
      | _ ->
        failwith
          "Couldn't convert all the statements connected within or to the supported ones"
    end
    (* Integer comparisons. *)
    | Expr.Relop (_ty, rel, lhs, rhs) ->
      let rel =
        match rel with
        | Ty.Relop.Eq -> fun t c -> Ir.eia (Ir.Eia.eq t c)
        | Ty.Relop.Ne -> fun t c -> Ir.lnot (Ir.eia (Ir.Eia.eq t c))
        | Ty.Relop.Le -> fun t c -> Ir.eia (Ir.Eia.leq t c)
        | Ty.Relop.Lt -> fun t c -> Ir.eia (Ir.Eia.lt t c)
        | Ty.Relop.Ge -> fun t c -> Ir.eia (Ir.Eia.geq t c)
        | Ty.Relop.Gt -> fun t c -> Ir.eia (Ir.Eia.gt t c)
        | _ -> failwith "Unsupported relational operator in EIA"
      in
      let lhs_term, lhs_c = expect_eia lhs in
      let rhs_term, rhs_c = expect_eia rhs in
      let atoms =
        Map.merge lhs_term rhs_term ~f:(fun ~key:_ vs ->
          match vs with
          | `Both (v1, v2) -> Some (v1 - v2)
          | `Left v -> Some v
          | `Right v -> Some (-v))
      in
      let c = rhs_c - lhs_c in
      let term = Ir.Eia.sum atoms in
      let ir = rel term c in
      `Ir ir
    (* Quantifiers and binders. *)
    | Expr.Binder (((Binder.Forall | Binder.Exists) as q), atoms, formula) ->
      let binder =
        match q with
        | Binder.Forall -> fun l f -> Ir.lnot (Ir.exists l (Ir.lnot f))
        | Binder.Exists -> Ir.exists
        | _ -> failwith "Unreachable"
      in
      let atoms =
        List.map
          begin
            fun atom ->
              match atom |> _to_ir with
              | `Symbol symbol -> Ir.var symbol
              | _ -> failwith "Unexpected value in quantifier"
          end
          atoms
      in
      begin
        match formula |> _to_ir with
        | `Ir formula -> `Ir (binder atoms formula)
        | _ ->
          failwith
            "Unable to convert the variable under the quantifier to the supported formula"
      end
    | Expr.Binder (Binder.Let_in, bindings, ir) -> begin
      match ir |> _to_ir with
      | `Ir ir ->
        `Ir
          (List.fold_left
             begin
               fun acc binding ->
                 match Expr.view binding with
                 | Expr.App (symbol, [ expr ]) ->
                   let symbol = Symbol.to_string symbol in
                   let var = Ir.Var symbol in
                   begin
                     match expr |> _to_ir with
                     | `Eia (Ir.Eia.Sum term, c) ->
                       assert (not (Map.mem term var));
                       let add_term (Ir.Eia.Sum term2) =
                         match Map.find term2 var with
                         | None -> Ir.Eia.Sum term2
                         | Some x ->
                           Ir.Eia.add
                             (Ir.Eia.mul x (Ir.Eia.Sum term))
                             (Ir.Eia.Sum (Map.remove term2 var))
                       in
                       let rec add_ir = function
                         (* TODO(timafrolov): how P(x + 5) will work? *)
                         | Ir.Pred (name, args) ->
                           Ir.Pred (name, args |> List.map add_term)
                         | Ir.True -> Ir.True
                         | Ir.Eia (Ir.Eia.Eq (Ir.Eia.Sum term2, c2) as x)
                         | Ir.Eia (Ir.Eia.Lt (Ir.Eia.Sum term2, c2) as x)
                         | Ir.Eia (Ir.Eia.Leq (Ir.Eia.Sum term2, c2) as x)
                         | Ir.Eia (Ir.Eia.Gt (Ir.Eia.Sum term2, c2) as x)
                         | Ir.Eia (Ir.Eia.Geq (Ir.Eia.Sum term2, c2) as x) ->
                           let constructor =
                             match x with
                             | Ir.Eia.Eq _ -> Ir.Eia.eq
                             | Ir.Eia.Lt _ -> Ir.Eia.lt
                             | Ir.Eia.Leq _ -> Ir.Eia.leq
                             | Ir.Eia.Gt _ -> Ir.Eia.gt
                             | Ir.Eia.Geq _ -> Ir.Eia.geq
                           in
                           Ir.Eia
                             (match Map.find term2 var with
                              | None -> x
                              | Some x ->
                                constructor (add_term (Ir.Eia.Sum term2)) (c2 - (c * x)))
                         | Ir.Bv _ ->
                           failwith "Unimplemented bitvectors in let-in binding"
                         | Ir.Lnot ir -> Ir.Lnot (add_ir ir)
                         | Ir.Land ir -> Ir.Land (ir |> List.map add_ir)
                         | Ir.Lor ir -> Ir.Lor (ir |> List.map add_ir)
                         | Ir.Exists (atoms, ir) ->
                           if atoms |> List.mem var
                           then Ir.Exists (atoms, ir)
                           else Ir.Exists (atoms, add_ir ir)
                       in
                       add_ir acc
                     | `Ir ir' ->
                       Ir.map
                         begin
                           function
                           | Pred (name, _) when name = symbol -> ir'
                           | ir -> ir
                         end
                         ir
                     | _ ->
                       Format.asprintf
                         "Unimplemented theory in let-in binding: %a"
                         Expr.pp
                         expr
                       |> failwith
                   end
                 | _ -> failwith "Unexpected construction in let-in binding"
             end
             ir
             bindings)
      | `Eia (Ir.Eia.Sum _term, _c) -> failwith ""
      | _ ->
        Format.asprintf
          "Unsupported expression %a within 'in' construction in 'let-in'"
          Expr.pp
          ir
        |> failwith
    end
    | _ -> Format.asprintf "Expression %a can't be handled" Expr.pp orig_expr |> failwith
  ;;
end

type state =
  { asserts : Lib.Ir.t list
  ; prev : state option
  }

let () =
  let f = Sys.argv.(1) |> Fpath.of_string |> Result.get_ok |> Smtml.Parse.from_file in
  let exec ({ prev; _ } as state) = function
    | Smtml.Ast.Push _ -> { asserts = []; prev = Some state }
    | Smtml.Ast.Pop _ -> begin
      match prev with
      | Some state -> state
      | None -> failwith "Nothing to pop"
    end
    | Smtml.Ast.Check_sat exprs ->
      let expr_irs =
        List.map
          begin
            fun expr ->
              match Conv._to_ir expr with
              | `Ir ir -> ir
              | _ -> failwith "Expected boolean formula"
          end
          exprs
      in
      let rec get_irs { asserts; prev; _ } =
        match prev with
        | Some state -> asserts @ get_irs state
        | None -> asserts
      in
      let ir = Lib.Ir.land_ (expr_irs @ get_irs state) in
      Lib.Debug.printfln "%a" Lib.Ir.pp ir;
      begin
        match Lib.Solver.proof ir with
        | `Sat -> Format.printf "sat\n%!"
        | `Unsat -> Format.printf "unsat\n%!"
        | `Unknown -> Format.printf "unknown\n%!"
      end;
      state
    | Smtml.Ast.Get_model ->
      let rec get_irs { asserts; prev; _ } =
        match prev with
        | Some state -> asserts @ get_irs state
        | None -> asserts
      in
      let ir = Lib.Ir.land_ (get_irs state) in
      begin
        match Lib.Solver.get_model ir with
        | Some model ->
          Map.iteri
            ~f:(fun ~key:k ~data:v -> Format.printf "%a = %d; " Lib.Ir.pp_atom k v)
            model;
          Format.printf "\n%!"
        | None -> Format.printf "no model\n%!"
      end;
      state
    (*| Smtml.Ast.Declare_const { id; _ } ->
      let var = Smtml.Symbol.to_string id in
      consts := var :: !consts;
      acc*)
    | Smtml.Ast.Assert expr -> begin
      match Conv._to_ir expr with
      | `Ir ir -> { state with asserts = ir :: state.asserts }
      | _ -> failwith "Expected boolean formula"
    end
    | _ -> state
  in
  let _ = List.fold_left exec { asserts = []; prev = None } f in
  ()
;;
