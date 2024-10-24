open Bits
open Utils
module Map = Nfa.Map

type varpos = int
type deg = int

type state = Eq | Neq

let add ~lhs ~rhs ~sum deg =
  Nfa.create_nfa
    ~transitions:
        [ (Eq, 0b000, Eq)
        ; (Eq, 0b101, Eq)
        ; (Eq, 0b110, Eq)
        ; (Eq, 0b011, Neq)
        ; (Neq, 0b111, Neq)
        ; (Neq, 0b010, Neq)
        ; (Neq, 0b001, Neq)
        ; (Neq, 0b100, Eq) ]
      ~start:[Eq] ~final:[Eq] ~vars:[lhs; rhs; sum] ~deg:32

let eq lhs rhs deg =
  Nfa.create_nfa
    ~transitions:
      [((), 0b00, ()); ((), 0b11, ())]
    ~start:[()] ~final:[()]
    ~vars:[lhs; rhs]
    ~deg:32

let eq_const var (n : int) deg =
  let bit_string = Bits.to_bit_string n in
  let max = List.length bit_string in
  Nfa.create_nfa ~start:[0] ~final:[max]
    ~transitions:
      ( (max, 0, max)
      :: (bit_string |> List.mapi (fun i bit -> let v = match bit with 
      | Bits.I -> 0b1
      | _ -> 0b0 in 
      (i, v, i + 1)))
      )
    ~vars:[var]
    ~deg:32

let n deg = Nfa.create_nfa ~transitions:[((), 0, ())] ~start:[()] ~final:[()] ~vars:[] ~deg:32
let z deg = Nfa.create_nfa ~transitions:[] ~start:[()] ~final:[] ~vars:[] ~deg:32

type leq_state = Eq | Neq

let leq lhs rhs deg =
    Nfa.create_nfa
      ~transitions:
        ( [ (Eq, 0b00, Eq)
          ; (Eq, 0b11, Eq)
          ; (Eq, 0b10, Eq)
          ; (Eq, 0b01, Neq)
          ; (Neq, 0b11, Neq)
          ; (Neq, 0b11, Neq)
          ; (Neq, 0b01, Neq)
          ; (Neq, 0b10, Eq) ])
        ~start:[Eq] 
        ~final:[Eq]
        ~vars:[lhs; rhs]
        ~deg:32

let geq x y = leq y x
