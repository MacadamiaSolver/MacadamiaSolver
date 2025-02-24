let nfa_cnt = ref 0
let flag () = Sys.getenv_opt "MANDAMS_DEBUG" |> Option.is_some

let dump_nfa ?show ?subdir ?name nfa =
  if flag ()
  then (
    let ( !< ) a = Format.sprintf a in
    let name =
      match name with
      | Some name -> name
      | None ->
        nfa_cnt := !nfa_cnt + 1;
        Format.sprintf "%d" !nfa_cnt
    in
    let show =
      match show with
      | Some show -> show
      | None -> false
    in
    let subdir =
      match subdir with
      | Some subdir -> subdir
      | None -> string_of_int (Unix.getpid ())
    in
    let supdir = "debugs" in
    Sys.command (!<{|mkdir -p "%s"/"%s"|} supdir subdir) |> ignore;
    let dir = !<"%s/%s" supdir subdir in
    let dot_file = !<"%s/%s.dot" dir name in
    let svg_file = !<"%s/%s.svg" dir name in
    let oc = open_out dot_file in
    let command = Format.sprintf {|dot -Tsvg "%s" > "%s"|} dot_file svg_file in
    Format.asprintf "%a" Nfa.format_nfa (nfa |> Nfa.minimize) |> Printf.fprintf oc "%s";
    close_out oc;
    Sys.command command |> ignore;
    if show then Sys.command (!<{|xdg-open "%s"|} svg_file) |> ignore;
    ())
;;

let out_formatter =
  (if flag () then Stdio.stderr else open_out "/dev/null")
  |> Format.formatter_of_out_channel
;;

let printf str = Format.fprintf out_formatter str
