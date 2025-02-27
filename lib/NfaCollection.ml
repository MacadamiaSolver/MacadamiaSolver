module Map = Nfa.Map

type varpos = int

let add ~lhs ~rhs ~sum =
  Nfa.create_nfa
    ~transitions:
      [ 0, 0b000, 0
      ; 0, 0b101, 0
      ; 0, 0b110, 0
      ; 0, 0b011, 1
      ; 1, 0b111, 1
      ; 1, 0b010, 1
      ; 1, 0b001, 1
      ; 1, 0b100, 0
      ]
    ~start:[ 0 ]
    ~final:[ 0 ]
    ~vars:[ sum; rhs; lhs ]
    ~deg:((max lhs rhs |> max sum) + 1)
;;

let eq lhs rhs =
  Nfa.create_nfa
    ~transitions:[ 0, 0b00, 0; 0, 0b11, 0 ]
    ~start:[ 0 ]
    ~final:[ 0 ]
    ~vars:[ lhs; rhs ]
    ~deg:(max lhs rhs + 1)
;;

let eq_const var (n : int) =
  let vec = Bitv.of_int_us n |> Bitv.to_list |> Bitv.of_list in
  let max = Bitv.length vec in
  let transitions =
    Bitv.foldi_right
      (fun i bit acc -> (i, (if bit then 1 else 0), i + 1) :: acc)
      vec
      [ max, 0, max ]
  in
  Nfa.create_nfa ~start:[ 0 ] ~final:[ max ] ~transitions ~vars:[ var ] ~deg:(var + 1)
;;

let n () =
  Nfa.create_nfa ~transitions:[ 0, 0, 0 ] ~start:[ 0 ] ~final:[ 0 ] ~vars:[] ~deg:1
;;

let z () = Nfa.create_nfa ~transitions:[] ~start:[ 0 ] ~final:[] ~vars:[] ~deg:1

let leq lhs rhs =
  Nfa.create_nfa
    ~transitions:
      [ 0, 0b00, 0
      ; 0, 0b11, 0
      ; 0, 0b10, 0
      ; 0, 0b01, 1
      ; 1, 0b11, 1
      ; 1, 0b00, 1
      ; 1, 0b01, 1
      ; 1, 0b10, 0
      ]
    ~start:[ 0 ]
    ~final:[ 0 ]
    ~vars:[ rhs; lhs ]
    ~deg:(max lhs rhs + 1)
;;

let geq x y = leq y x

let lt lhs rhs =
  Nfa.create_nfa
    ~transitions:
      [ 0, 0b01, 1
      ; 0, 0b11, 0
      ; 0, 0b10, 0
      ; 0, 0b00, 0
      ; 1, 0b11, 1
      ; 1, 0b01, 1
      ; 1, 0b00, 1
      ; 1, 0b10, 0
      ]
    ~start:[ 0 ]
    ~final:[ 1 ]
    ~vars:[ lhs; rhs ]
    ~deg:(max lhs rhs + 1)
;;

let gt x y = lt y x

let torename var a c =
  if c = 0
  then (
    let trans1 = List.init a Fun.id |> List.map (fun x -> x, 0b0, x + 1) in
    Nfa.create_nfa
      ~transitions:([ a, 0b1, a + 1; a + 1, 0b0, a + 1 ] @ trans1)
      ~start:[ 0 ]
      ~final:[ a + 1 ]
      ~vars:[ var ]
      ~deg:(var + 1))
  else (
    let trans1 = List.init (a + c - 1) Fun.id |> List.map (fun x -> x, 0b0, x + 1) in
    Nfa.create_nfa
      ~transitions:([ a + c - 1, 0b0, a; a, 0b1, a + c; a + c, 0b0, a + c ] @ trans1)
      ~start:[ 0 ]
      ~final:[ a + c ]
      ~vars:[ var ]
      ~deg:(var + 1))
;;

let torename2 var exp =
  Nfa.create_nfa
    ~transitions:[ 0, 0b10, 0; 0, 0b00, 0; 0, 0b11, 1; 1, 0b00, 1 ]
    ~start:[ 0 ]
    ~final:[ 1 ]
    ~vars:[ var; exp ]
    ~deg:(max var exp + 1)
;;

let power_of_two exp =
  Nfa.create_nfa
    ~transitions:[ 0, 0b0, 0; 0, 0b1, 1; 1, 0b0, 1 ]
    ~start:[ 0 ]
    ~final:[ 1 ]
    ~vars:[ exp ]
    ~deg:(exp + 1)
;;

let mul ~res ~lhs ~rhs =
  let rec helper ~res ~lhs ~rhs =
    match lhs with
    | 0 -> eq_const res 0
    | 1 -> eq res rhs
    | _ when lhs mod 2 = 0 ->
      let newvar = max (max res lhs) rhs + 1 in
      let a = helper ~res:newvar ~lhs:(lhs / 2) ~rhs in
      let b = add ~sum:res ~lhs:newvar ~rhs:newvar in
      Nfa.intersect a b |> Nfa.project [ newvar ]
    | _ ->
      let newvar = max (max res lhs) rhs + 1 in
      let a = helper ~res:newvar ~lhs:(lhs - 1) ~rhs in
      let b = add ~sum:res ~lhs:newvar ~rhs in
      Nfa.intersect a b |> Nfa.project [ newvar ]
  in
  helper ~res ~lhs ~rhs |> Nfa.minimize
;;
