open Lib
module Map = Base.Map.Poly

type state =
  { asserts : Ast.formula list
  ; vars : string list
  ; logic : string
  }

let init = { asserts = []; vars = []; logic = "LIA" }
let ( let* ) = Result.bind
let return = Result.ok
let set_logic state logic' = { state with logic = logic' }

let add_assert' ({ asserts; _ } as state) assert' =
  { state with asserts = assert' :: asserts }
;;

let add_var ({ vars; _ } as state) var = { state with vars = var :: vars }

let run { asserts; vars; logic; _ } =
  match asserts with
  | h :: tl ->
    (match logic with
     | "ALL" ->
       List.fold_left Ast.mand h tl
       |> (fun f ->
       Debug.printfln "Formula to proof: %a" Ast.pp_formula f;
       f)
       |> Solver.proof_semenov
       |> Result.get_ok
     | _ ->
       List.fold_left Ast.mand h tl
       |> (fun f -> Ast.exists vars f)
       |> (fun f ->
       Debug.printfln "Formula to proof: %a" Ast.pp_formula f;
       f)
       |> Solver.proof
       |> Result.get_ok)
  | [] -> true
;;

let getmodel { asserts; vars; logic; _ } =
  match asserts with
  | h :: tl ->
    (match logic with
     | "ALL" -> Result.error "Semenov arithmetic doesn't support getting a model yet"
     | _ ->
       List.fold_left Ast.mand h tl |> (fun f -> Ast.exists vars f) |> Solver.get_model)
  | [] -> Result.error "No assertions are made to get model for"
;;

let command s = function
  | Smtlib.SetLogic logic -> set_logic s logic |> Result.ok
  | Smtlib.Assert' f ->
    let* f = Smtlib.to_formula f in
    add_assert' s f |> return
  | Smtlib.DeclareFun (f, _sorts, _sort) -> f |> add_var s |> Result.ok
  | Smtlib.CheckSat ->
    let res = run s in
    if res then Format.printf "sat%!\n" else Format.printf "unsat%!\n";
    s |> Result.ok
  | Smtlib.GetModel ->
    (match getmodel s with
     | Ok model ->
       (match model with
        | Some model ->
          Map.iteri ~f:(fun ~key:k ~data:v -> Format.printf "%s = %d  " k v) model;
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
  let s = read_whole_file filename |> Smtlib.parse |> Result.get_ok in
  script init s |> Result.get_ok
;;
