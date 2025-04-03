module Map = Base.Map.Poly

let ( let* ) = Option.bind

let option_map_to_map_option (map : ('a, 'b option) Map.t) : ('a, 'b) Map.t option =
  Map.fold map ~init:(Some Map.empty) ~f:(fun ~key ~data acc ->
    let* acc = acc in
    let* data = data in
    Some (Map.set ~key ~data acc))
;;

let pow2 n = List.init n (Fun.const 2) |> List.fold_left ( * ) 1
