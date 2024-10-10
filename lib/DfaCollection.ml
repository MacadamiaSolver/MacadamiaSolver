open Bits
open Utils
module Map = Dfa.Map

let ( let* ) = Option.bind

let l (a, b, c) =
  let* b =
    b |> Map.of_alist_multi
    |> Map.map ~f:(function
         | [] ->
             None
         | h :: tl ->
             if List.for_all (( = ) h) tl then Some h else None )
    |> option_map_to_map_option
  in
  Some (a, b, c)

type addState = Eq | Neq

let add ~lhs ~rhs ~sum =
  Dfa.create
    ~transitions:
      ( [ l (Eq, [(lhs, O); (rhs, O); (sum, O)], Eq)
        ; l (Eq, [(lhs, I); (rhs, O); (sum, I)], Eq)
        ; l (Eq, [(lhs, O); (rhs, I); (sum, I)], Eq)
        ; l (Eq, [(lhs, I); (rhs, I); (sum, O)], Neq)
        ; l (Neq, [(lhs, I); (rhs, I); (sum, I)], Neq)
        ; l (Neq, [(lhs, O); (rhs, I); (sum, O)], Neq)
        ; l (Neq, [(lhs, I); (rhs, O); (sum, O)], Neq)
        ; l (Neq, [(lhs, O); (rhs, O); (sum, I)], Eq) ]
      |> List.filter_map Fun.id )
    ~start:Eq ~final:[Eq]

let eq lhs rhs =
  Dfa.create
    ~transitions:
      ( [l ((), [(lhs, O); (rhs, O)], ()); l ((), [(lhs, I); (rhs, I)], ())]
      |> List.filter_map Fun.id )
    ~start:() ~final:[()]

let eq_const var (n : int) =
  let l = Dfa.Map.of_alist_exn in
  let bit_string = Bits.to_bit_string n in
  let max = List.length bit_string in
  Dfa.create ~start:0 ~final:[max]
    ~transitions:
      ( (max, l [(var, O)], max)
      :: (bit_string |> List.mapi (fun i bit -> (i, l [(var, bit)], i + 1))) )

let any () = Dfa.create ~transitions:[((), Map.empty, ())] ~start:() ~final:[()]

let none () = Dfa.create ~transitions:[] ~start:() ~final:[]
