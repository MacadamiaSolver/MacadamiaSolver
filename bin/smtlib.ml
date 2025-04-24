open Lib
module Map = Base.Map.Poly

type var =
  { name : string
  ; sort : string
  }

type state =
  { asserts : Ast.formula list
  ; vars : var list
  }

let init = { asserts = []; vars = [] }
let ( let* ) = Result.bind
let return = Result.ok

let add_assert' ({ asserts; _ } as state) assert' =
  { state with asserts = assert' :: asserts }
;;

let add_var ({ vars; _ } as state) name = function
  (* TODO: support sort parameters *)
  | Smtlib.Sort (sort, _) -> { state with vars = { name; sort } :: vars }
;;

let run { asserts; vars; _ } =
  match asserts with
  | h :: tl ->
    List.fold_left Ast.mand h tl
    |> (fun f -> Ast.exists (vars |> List.map (fun var -> var.name)) f)
    |> (fun f ->
    Debug.printfln "Formula to proof: %a" Ast.pp_formula f;
    f)
    |> Solver.proof
  | [] -> true |> return
;;

let getmodel { asserts; _ } =
  match asserts with
  | h :: tl -> List.fold_left Ast.mand h tl |> Solver.get_model
  | [] -> Result.error "No assertions are made to get model for"
;;

let command ({ vars; _ } as s) = function
  | Smtlib.SetLogic logic ->
    (match logic with
     | "ALL" | "LIA" | "QF_LIA" | "QF_BV" -> return s
     | logic -> Format.sprintf "Logic %s is not supported" logic |> Result.error)
  | Smtlib.Assert' f ->
    let* f = Smtlib.to_formula f in
    add_assert' s f |> return
  | Smtlib.DeclareFun (f, _sorts, sort) -> add_var s f sort |> Result.ok
  | Smtlib.CheckSat ->
    let res = run s in
    (match res with
     | Result.Ok res -> if res then Format.printf "sat%!\n" else Format.printf "unsat%!\n"
     | Result.Error err -> Format.printf "unable to evaluate expression: %s" err);
    s |> Result.ok
  | Smtlib.GetModel ->
    (match getmodel s with
     | Ok model ->
       (match model with
        | Some model ->
          Map.iteri
            ~f:(fun ~key:varname ~data:value ->
              let var = List.find (fun var -> var.name = varname) vars in
              if String.starts_with ~prefix:"BitVec" var.sort
              then
                Format.printf
                  "%s = 0b%a (%d) "
                  var.name
                  Bitv.M.print
                  (Bitv.of_int_s value |> Bitv.to_list |> Bitv.of_list)
                  value
              else Format.printf "%s = %d  " var.name value)
            model;
          Format.printf "\n%!"
        | None -> Format.printf "No model\n%!")
     | Error msg -> Format.printf "Unable to get model: %s%!\n" msg);
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
  let s = read_whole_file filename |> Smtlib.parse in
  match s with
  | Result.Ok s ->
    Debug.printf
      "parsed smtlib: %a\n"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         Smtlib.pp_command)
      s;
    (match script init s with
     | Result.Ok () -> ()
     | Result.Error err -> Format.printf "error during script evaluation: %s\n" err)
  | Result.Error err -> Format.printf "error during parsing script: %s\n" err
;;
