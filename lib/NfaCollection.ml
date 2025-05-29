(* SPDX-License-Identifier: MIT *)
(* Copyright 2024-2025, Chrobelias. *)

module Map = Nfa.Map

type varpos = int

module type Type = sig
  type t

  val add : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val eq : varpos -> varpos -> t
  val eq_const : varpos -> int -> t
  val n : unit -> t
  val z : unit -> t
  val leq : varpos -> varpos -> t
  val geq : varpos -> varpos -> t
  val lt : varpos -> varpos -> t
  val gt : varpos -> varpos -> t
  val power_of_two : int -> t
  val bvor : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val bvand : lhs:varpos -> rhs:varpos -> res:varpos -> t
  val bvxor : lhs:varpos -> rhs:varpos -> res:varpos -> t
end

module Lsb = struct
  module Nfa = Nfa.Lsb

  let add ~lhs ~rhs ~res =
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
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let eq lhs rhs =
    Nfa.create_nfa
      ~transitions:[ 0, 0b00, 0; 0, 0b11, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ lhs; rhs ]
      ~deg:(max lhs rhs + 1)
  ;;

  let neq lhs rhs =
    Nfa.create_nfa
      ~transitions:
        [ 0, 0b00, 0
        ; 0, 0b11, 0
        ; 0, 0b01, 1
        ; 0, 0b10, 1
        ; 1, 0b00, 1
        ; 1, 0b01, 1
        ; 1, 0b10, 1
        ; 1, 0b11, 1
        ]
      ~start:[ 0 ]
      ~final:[ 1 ]
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
        let b = add ~res ~lhs:newvar ~rhs:newvar in
        Nfa.intersect a b |> Nfa.project [ newvar ]
      | _ ->
        let newvar = max (max res lhs) rhs + 1 in
        let a = helper ~res:newvar ~lhs:(lhs - 1) ~rhs in
        let b = add ~res ~lhs:newvar ~rhs in
        Nfa.intersect a b |> Nfa.project [ newvar ]
    in
    helper ~res ~lhs ~rhs |> Nfa.minimize
  ;;

  let bvand ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b001, 0; 0, 0b010, 0; 0, 0b111, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let bvor ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b101, 0; 0, 0b110, 0; 0, 0b111, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let bvxor ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b101, 0; 0, 0b110, 0; 0, 0b011, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;
end

module Msb = struct
  module Nfa = Nfa.Msb

  let add ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:
        [ 0, 0b000, 0
        ; 0, 0b101, 0
        ; 0, 0b001, 1
        ; 0, 0b011, 0
        ; 1, 0b111, 1
        ; 1, 0b010, 1
        ; 1, 0b100, 1
        ; 1, 0b110, 0
        ; 2, 0b000, 0
        ; 2, 0b011, 0
        ; 2, 0b101, 0
        ; 2, 0b100, 1
        ; 2, 0b010, 1
        ; 2, 0b111, 1
        ]
      ~start:[ 2 ]
      ~final:[ 0 ]
      ~vars:[ lhs; rhs; res ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let eq lhs rhs =
    Nfa.create_nfa
      ~transitions:[ 0, 0b00, 0; 0, 0b11, 0; 1, 0b00, 0; 1, 0b11, 0 ]
      ~start:[ 1 ]
      ~final:[ 0 ]
      ~vars:[ lhs; rhs ]
      ~deg:(max lhs rhs + 1)
  ;;

  let eq_const var (n : int) =
    let transitions, max =
      let rec helper acc cnt v =
        let d = if v mod 2 = 0 then 0 else 1 in
        let v' = (v - d) / 2 in
        if v' = v
        then (cnt, d, cnt) :: acc, cnt
        else (
          let nxt = succ cnt in
          helper ((nxt, d, cnt) :: acc) nxt v')
      in
      helper [] 0 n
    in
    let transitions = (max + 1, (if n >= 0 then 0 else 1), max) :: transitions in
    Nfa.create_nfa
      ~start:[ max + 1 ]
      ~final:[ 0 ]
      ~transitions
      ~vars:[ var ]
      ~deg:(var + 1)
  ;;

  let minus arg res =
    Nfa.create_nfa
      ~transitions:
        [ 0, 0b01, 0
        ; 0, 0b10, 0
        ; 0, 0b11, 1
        ; 1, 0b00, 1
        ; 2, 0b01, 0
        ; 2, 0b10, 0
        ; 2, 0b00, 1
        ]
      ~start:[ 2 ]
      ~final:[ 1 ]
      ~vars:[ arg; res ]
      ~deg:(max arg res + 1)
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
        ; 0, 0b01, 0
        ; 1, 0b10, 0
        ; 1, 0b11, 1
        ; 1, 0b00, 1
        ; 1, 0b10, 1
        ; 0, 0b01, 1
        ; 2, 0b11, 0
        ; 2, 0b00, 0
        ; 2, 0b10, 0
        ; 2, 0b10, 1
        ]
      ~start:[ 2 ]
      ~final:[ 0 ]
      ~vars:[ lhs; rhs ]
      ~deg:(max lhs rhs + 1)
  ;;

  let geq x y = leq y x

  let geq_zero x =
    Nfa.create_nfa
      ~transitions:[ 0, 0b0, 1; 1, 0b0, 1; 1, 0b1, 1 ]
      ~start:[ 0 ]
      ~final:[ 1 ]
      ~vars:[ x ]
      ~deg:(x + 1)
  ;;

  let lt lhs rhs =
    Nfa.create_nfa
      ~transitions:
        [ 0, 0b11, 0
        ; 0, 0b00, 0
        ; 0, 0b01, 1
        ; 1, 0b11, 1
        ; 1, 0b01, 1
        ; 1, 0b00, 1
        ; 1, 0b10, 1
        ; 2, 0b10, 1
        ; 2, 0b00, 0
        ; 2, 0b11, 0
        ]
      ~start:[ 2 ]
      ~final:[ 1 ]
      ~vars:[ lhs; rhs ]
      ~deg:(max lhs rhs + 1)
  ;;

  let gt x y = lt y x

  let power_of_two exp =
    Nfa.create_nfa
      ~transitions:[ 0, 0b0, 0; 0, 0b1, 1; 1, 0b0, 1; 2, 0b0, 0 ]
      ~start:[ 2 ]
      ~final:[ 1 ]
      ~vars:[ exp ]
      ~deg:(exp + 1)
  ;;

  let bvand ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b001, 0; 0, 0b010, 0; 0, 0b111, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let bvor ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b101, 0; 0, 0b110, 0; 0, 0b111, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;

  let bvxor ~lhs ~rhs ~res =
    Nfa.create_nfa
      ~transitions:[ 0, 0b000, 0; 0, 0b101, 0; 0, 0b110, 0; 0, 0b011, 0 ]
      ~start:[ 0 ]
      ~final:[ 0 ]
      ~vars:[ res; rhs; lhs ]
      ~deg:((max lhs rhs |> max res) + 1)
  ;;
end

module MsbNat = struct
  let eq lhs rhs = Msb.eq lhs rhs |> Nfa.to_nat
  let add ~lhs ~rhs ~res = Msb.add ~res ~lhs ~rhs |> Nfa.to_nat
  let eq_const res n = Msb.eq_const res n |> Nfa.to_nat
  let geq lhs rhs = Msb.geq lhs rhs |> Nfa.to_nat

  let mul ~res ~lhs ~rhs =
    let rec helper ~res ~lhs ~rhs =
      match lhs with
      | 0 -> eq_const res 0
      | 1 -> eq res rhs
      | _ when lhs mod 2 = 0 ->
        let newvar = max (max res lhs) rhs + 1 in
        let a = helper ~res:newvar ~lhs:(lhs / 2) ~rhs in
        let b = add ~res ~lhs:newvar ~rhs:newvar in
        Nfa.MsbNat.intersect a b |> Nfa.MsbNat.project [ newvar ]
      | _ ->
        let newvar = max (max res lhs) rhs + 1 in
        let a = helper ~res:newvar ~lhs:(lhs - 1) ~rhs in
        let b = add ~res ~lhs:newvar ~rhs in
        Nfa.MsbNat.intersect a b |> Nfa.MsbNat.project [ newvar ]
    in
    helper ~res ~lhs ~rhs |> Nfa.MsbNat.minimize
  ;;

  let torename var a c =
    if c = 0
    then (
      let trans1 = List.init a Fun.id |> List.map (fun x -> x + 1, 0b0, x) in
      let nfa =
        Nfa.MsbNat.create_nfa
          ~transitions:([ a + 1, 0b1, a; a + 1, 0b0, a + 1 ] @ trans1)
          ~start:[ a + 1 ]
          ~final:[ 0 ]
          ~vars:[ var ]
          ~deg:(var + 1)
      in
      Debug.printfln "Building torename nfa: var=%d, a=%d, c=%d" var a c;
      Debug.dump_nfa ~msg:"Nfa: %s" Nfa.MsbNat.format_nfa nfa;
      nfa)
    else (
      let trans1 = List.init (a + c - 1) Fun.id |> List.map (fun x -> x, 0b0, x + 1) in
      Nfa.MsbNat.create_nfa
        ~transitions:([ a + c - 1, 0b0, a; a, 0b1, a + c; a + c, 0b0, a + c ] @ trans1)
        ~start:[ 0 ]
        ~final:[ a + c ]
        ~vars:[ var ]
        ~deg:(var + 1))
  ;;

  let torename2 var exp =
    Nfa.MsbNat.create_nfa
      ~transitions:[ 0, 0b10, 0; 0, 0b00, 0; 1, 0b11, 0; 1, 0b00, 1 ]
      ~start:[ 1 ]
      ~final:[ 0 ]
      ~vars:[ var; exp ]
      ~deg:(max var exp + 1)
  ;;
end
