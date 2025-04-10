val flag : unit -> bool
val fmt : Format.formatter
val printf : ('a, Format.formatter, unit) format -> 'a
val printfln : ('a, Format.formatter, unit) format -> 'a

val dump_nfa
  :  ?msg:(string -> unit, Format.formatter, unit) format
  -> ?vars:(string * int) list
  -> (Format.formatter -> 'a -> unit)
  -> 'a
  -> unit
