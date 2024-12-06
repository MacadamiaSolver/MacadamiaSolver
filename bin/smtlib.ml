open Lib

type state =
  { asserts : Ast.formula list
  ; vars : string list
  }

let init = { asserts = []; vars = [] }
let ( let* ) = Result.bind
let return = Result.ok

let rec term s = function
  | Smtlib.Apply (f, _, ts) ->
    let top2 ast =
      let* t1 = List.nth_opt ts 0 |> Option.to_result ~none:"expected an argument" in
      let* t1 = t1 |> term s in
      let* t2 = List.nth_opt ts 1 |> Option.to_result ~none:"expected an argument" in
      let* t2 = t2 |> term s in
      ast t1 t2 |> return
    in
    let tiop ast =
      let* t1 = List.nth_opt ts 0 |> Option.to_result ~none:"expected an argument" in
      let* t1 = t1 |> term s in
      let* t2 = List.nth_opt ts 1 |> Option.to_result ~none:"expected an argument" in
      let* t2 = t2 |> term s in
      match t1, t2 with
      | Ast.Const d, _ -> ast d t2 |> return
      | _, Ast.Const d -> ast d t1 |> return
      | _ ->
        "this operator is only supported between a constant and a term" |> Result.error
    in
    (match f with
     | "+" -> top2 Ast.add
     | "exp" -> tiop Ast.pow
     | "*" -> tiop Ast.mul
     | _ -> Ast.var f |> return)
  | Smtlib.SpecConstant c ->
    (match c with
     | Smtlib.Numeric d -> Ast.const d |> return
     | _ -> "Unknown constant type" |> Result.error)
  | _ as t -> Format.asprintf "Expected term, found %a" Smtlib.pp_term t |> Result.error
;;

let rec formula s = function
  | Smtlib.Forall (vars, t) ->
    let vars = vars |> List.map fst in
    let* f = formula s t in
    Ast.any vars f |> return
  | Smtlib.Exists (vars, t) ->
    let vars = vars |> List.map fst in
    let* f = formula s t in
    Ast.exists vars f |> return
  | Smtlib.Apply (f, _, ts) ->
    let fop1 ast =
      let* t1 = List.nth_opt ts 0 |> Option.to_result ~none:"expected an argument" in
      let* t1 = formula s t1 in
      ast t1 |> return
    in
    let fop2 ast =
      let* f1 = List.nth_opt ts 0 |> Option.to_result ~none:"expected an argument" in
      let* f1 = f1 |> formula s in
      let* f2 = List.nth_opt ts 1 |> Option.to_result ~none:"expected an argument" in
      let* f2 = f2 |> formula s in
      ast f1 f2 |> return
    in
    let top2 ast =
      let* t1 = List.nth_opt ts 0 |> Option.to_result ~none:"expected an argument" in
      let* t1 = t1 |> term s in
      let* t2 = List.nth_opt ts 1 |> Option.to_result ~none:"expected an argument" in
      let* t2 = t2 |> term s in
      ast t1 t2 |> return
    in
    let cf ast =
      match ts with
      | t :: tl ->
        let* t = formula s t in
        List.fold_left
          (fun acc t ->
             let* f = formula s t in
             let* acc = acc in
             ast acc f |> return)
          (t |> return)
          tl
      | [] -> failwith "expected at least 1 argument"
    in
    (match f with
     | "=" ->
       (match top2 Ast.eq with
        | Ok r -> r |> return
        | Error _ ->
          (match cf Ast.mand with
           | Ok r -> r |> return
           | Error _ ->
             "'=' expected all arguments to be formulas or terms" |> Result.error))
     | "<=" -> top2 Ast.leq
     | ">=" -> top2 Ast.geq
     | "<" -> top2 Ast.lt
     | ">" -> top2 Ast.gt
     | "not" -> fop1 Ast.mnot
     | "and" -> fop2 Ast.mand
     | "or" -> fop2 Ast.mor
     | "=>" -> fop2 Ast.mimpl
     | _ -> Result.error "uninmplemented")
    (* TODO: string is ignored *)
  | _ -> Result.error "uninmplemented"
;;

let add_assert' ({ asserts; _ } as state) assert' =
  { state with asserts = assert' :: asserts }
;;

let add_var ({ vars; _ } as state) var = { state with vars = var :: vars }

let run { asserts; vars; _ } =
  match asserts with
  | h :: tl ->
    List.fold_left Ast.mand h tl
    |> (fun f -> Ast.exists vars f)
    |> Solver.proof
    |> Result.get_ok
  | [] -> true
;;

let command s = function
  | Smtlib.Assert' f ->
    let* f = formula s f in
    add_assert' s f |> return
  | Smtlib.DeclareFun (f, _sorts, _sort) -> f |> add_var s |> Result.ok
  | Smtlib.CheckSat ->
    let res = run s in
    Format.printf "Result: %b \n" res;
    s |> Result.ok
  | _ -> s |> Result.ok
;;

let rec script s = function
  | c :: tl ->
    let* s = command s c in
    script s tl
  | [] -> Result.ok ()
;;

(* Stolen from https://stackoverflow.com/questions/53839695/how-do-i-read-the-entire-content-of-a-given-file-into-a-string *)
let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s
;;

let () =
  let filename = Array.get Sys.argv 1 in
  let s = read_whole_file filename |> Smtlib.parse |> Result.get_ok in
  (*Format.printf
    "%a@."
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n")
       Smtlib.pp_command)
    s;*)
  script init s |> Result.get_ok
;;

(* *)
