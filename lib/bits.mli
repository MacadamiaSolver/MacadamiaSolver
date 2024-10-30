type bit = I | O

val to_bit_string : int -> bit list

val zip3 : bit list -> bit list -> bit list -> (bit * bit * bit) list

val pp_print_bit : Format.formatter -> bit -> unit
