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
  let trans1 = List.init (a + c - 1) Fun.id |> List.map (fun x -> x, 0b0, x + 1) in
  Nfa.create_nfa
    ~transitions:([ a + c - 1, 0b0, a; a, 0b1, a + c; a + c, 0b0, a + c ] @ trans1)
    ~start:[ 0 ]
    ~final:[ a + c ]
    ~vars:[ var ]
    ~deg:(var + 1)
;;
