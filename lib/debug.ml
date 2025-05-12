let nfa_cnt = ref 0
let flag () = Sys.getenv_opt "CHRO_DEBUG" |> Option.is_some

let fmt =
  if flag ()
  then Format.formatter_of_out_channel Stdio.stderr
  else
    Format.formatter_of_out_functions
      { out_string = (fun _ _ _ -> ())
      ; out_flush = (fun _ -> ())
      ; out_newline = (fun _ -> ())
      ; out_spaces = (fun _ -> ())
      ; out_indent = (fun _ -> ())
      }
;;

let printf str = Format.fprintf fmt (str ^^ "%!")
let printfln str = Format.fprintf fmt (str ^^ "\n%!")

let dump_nfa ?msg ?vars format_nfa nfa =
  if flag ()
  then (
    let ( !< ) a = Format.sprintf a in
    let name =
      nfa_cnt := !nfa_cnt + 1;
      Format.sprintf "%d" !nfa_cnt
    in
    let subdir = string_of_int (Unix.getpid ()) in
    let supdir = "debugs" in
    Sys.command (!<{|mkdir -p "%s"/"%s"|} supdir subdir) |> ignore;
    let dir = !<"%s/%s" supdir subdir in
    let dot_file = !<"%s/%s.dot" dir name in
    let svg_file = !<"%s/%s.svg" dir name in
    let oc = open_out dot_file in
    let command = Format.sprintf {|dot -Tsvg "%s" > "%s"|} dot_file svg_file in
    Format.asprintf "%a" format_nfa nfa |> Printf.fprintf oc "%s";
    close_out oc;
    Sys.command command |> ignore;
    (match msg with
     | Some msg -> printfln msg svg_file
     | None -> ());
    match vars with
    | Some vars ->
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n")
        (fun fmt (a, b) -> Format.fprintf fmt "%d -> %s" b a)
        fmt
        vars;
      printfln "\n"
    | None -> ())
;;
