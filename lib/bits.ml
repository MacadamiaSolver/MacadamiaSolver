type bit = I | O

let to_bit_string n =
  let rec helper acc n i =
    if i = 63 then acc
    else if n mod 2 = 0 then helper (O :: acc) (n / 2) (i + 1)
    else helper (I :: acc) (n / 2) (i + 1)
  in
  helper [] n 0 |> List.rev

let is_empty = function _ :: _ -> false | [] -> true

let rec zip3 n1 n2 n3 =
  if is_empty n1 && is_empty n2 && is_empty n3 then []
  else
    let h1 = if List.is_empty n1 then O else List.hd n1 in
    let h2 = if List.is_empty n2 then O else List.hd n2 in
    let h3 = if List.is_empty n3 then O else List.hd n3 in
    let tl1 = if List.is_empty n1 then [] else List.tl n1 in
    let tl2 = if List.is_empty n2 then [] else List.tl n2 in
    let tl3 = if List.is_empty n3 then [] else List.tl n3 in
    (h1, h2, h3) :: zip3 tl1 tl2 tl3
