val list : unit -> unit

val pred : string -> string list -> Ast.formula -> (unit, string) result

val dump : Ast.formula -> (string, string) result

val proof : Ast.formula -> (bool, string) result

val proof_chrobak : Ast.formula -> (bool, string) result
