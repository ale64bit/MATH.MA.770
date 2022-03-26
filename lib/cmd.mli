type mode = Classic | Intuitionistic

type cmd =
  | Axiom of LK.formula
  | Premise of LK.sequent
  | Weakening of LK.side * int * LK.formula
  | Contraction of LK.side * int
  | Exchange of LK.side * int * int
  | Cut of int * int
  | Negation of LK.side * int
  | ConjLeft of LK.side * int * LK.formula
  | ConjRight of int * int
  | DisjLeft of int * int
  | DisjRight of LK.side * int * LK.formula
  | ImplLeft of int * int
  | ImplRight of int
  | ForAllLeft of int * LK.term * LK.var
  | ForAllRight of int * LK.var * LK.var
  | ExistsLeft of int * LK.var * LK.var
  | ExistsRight of int * LK.term * LK.var
  | Macro of string * (LK.formula * LK.formula) list
  | Load of string
  | Save of string
  | Print
  | TeX of string
  | Clear
  | Mode of mode

val string_of_mode : mode -> string
val string_of_cmd : cmd -> string
val ascii_string_of_cmd : cmd -> string
