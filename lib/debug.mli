val flag : unit -> bool
val fmt : Format.formatter
val printf : ('a, Format.formatter, unit) format -> 'a
val printfln : ('a, Format.formatter, unit) format -> 'a

val dump_nfa
  :  ?msg:(string -> unit, Format.formatter, unit, unit, unit, unit) format6
  -> ?vars:(string * int) list
  -> (Format.formatter -> 'a -> unit)
  -> 'a
  -> unit
