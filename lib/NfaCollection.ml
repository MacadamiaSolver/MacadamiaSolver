module Map = Nfa.Map

type varpos = int

type deg = int

let add ~lhs ~rhs ~sum _ =
  Nfa.create_nfa
    ~transitions:
      [ [(0b000, 0); (0b101, 0); (0b110, 0); (0b011, 1)]
      ; [(0b111, 1); (0b010, 1); (0b001, 1); (0b100, 0)] ]
    ~start:[0] ~final:[0] ~vars:[lhs; rhs; sum] ~deg:32

let eq lhs rhs _ =
  Nfa.create_nfa
    ~transitions:[[(0b00, 0); (0b11, 0)]]
    ~start:[0] ~final:[0] ~vars:[lhs; rhs] ~deg:32

let eq_const var (n : int) _ =
  let vec = Bitv.of_int_us n |> Bitv.to_list |> Bitv.of_list in
  let max = Bitv.length vec in
  let transitions =
    Bitv.foldi_right
      (fun i bit acc -> [((if bit then 1 else 0), i + 1)] :: acc)
      vec
      [[(0, max)]]
  in
  Nfa.create_nfa ~start:[0] ~final:[max] ~transitions ~vars:[var] ~deg:32

let n _ =
  Nfa.create_nfa ~transitions:[[(0, 0)]] ~start:[0] ~final:[0] ~vars:[] ~deg:32

let z _ = Nfa.create_nfa ~transitions:[[]] ~start:[0] ~final:[] ~vars:[] ~deg:32

let leq lhs rhs _ =
  Nfa.create_nfa
    ~transitions:
      [ [(0b00, 0); (0b11, 0); (0b10, 0); (0b01, 1)]
      ; [(0b11, 1); (0b00, 1); (0b01, 1); (0b10, 0)] ]
    ~start:[0] ~final:[0] ~vars:[lhs; rhs] ~deg:32

let geq x y = leq y x
