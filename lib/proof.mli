type proof

val empty : proof
val add : LK.sequent -> LK.inference -> Cmd.cmd -> proof -> int * proof
val resolve : int -> proof -> (LK.sequent, string) result
val axioms_and_endsequent : proof -> LK.sequent list * LK.sequent
val string_of_derivation : proof -> LK.inference -> string
val print_proof : proof -> unit
val tex_of_proof : proof -> string
val string_of_proof_cmds : proof -> string
