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

let string_of_mode = function Classic -> "LK" | Intuitionistic -> "LJ"

let gen_string_of_cmd sos sof sot sov = function
  | Axiom f -> Printf.sprintf "axiom %s" (sof f)
  | Premise s -> Printf.sprintf "premise %s" (sos s)
  | Weakening (side, i, f) ->
      Printf.sprintf "%sweak %d %s"
        (String.lowercase_ascii (LK.string_of_side side))
        i (sof f)
  | Contraction (side, i) ->
      Printf.sprintf "%scont %d"
        (String.lowercase_ascii (LK.string_of_side side))
        i
  | Exchange (side, i, j) ->
      Printf.sprintf "%sexch %d %d"
        (String.lowercase_ascii (LK.string_of_side side))
        i j
  | Cut (i, j) -> Printf.sprintf "cut %d %d" i j
  | Negation (side, i) ->
      Printf.sprintf "%sneg %d"
        (String.lowercase_ascii (LK.string_of_side side))
        i
  | ConjLeft (side, i, f) ->
      Printf.sprintf "%slconj %d %s"
        (String.lowercase_ascii (LK.string_of_side side))
        i (sof f)
  | ConjRight (i, j) -> Printf.sprintf "rconj %d %d" i j
  | DisjLeft (i, j) -> Printf.sprintf "ldisj %d %d" i j
  | DisjRight (side, i, f) ->
      Printf.sprintf "%srdisj %d %s"
        (String.lowercase_ascii (LK.string_of_side side))
        i (sof f)
  | ImplLeft (i, j) -> Printf.sprintf "limpl %d %d" i j
  | ImplRight i -> Printf.sprintf "rimpl %d" i
  | ForAllLeft (i, t, x) -> Printf.sprintf "lforall %d %s %s" i (sot t) (sov x)
  | ForAllRight (i, a, x) -> Printf.sprintf "rforall %d %s %s" i (sov a) (sov x)
  | ExistsLeft (i, a, x) -> Printf.sprintf "lexists %d %s %s" i (sov a) (sov x)
  | ExistsRight (i, t, x) -> Printf.sprintf "rexists %d %s %s" i (sot t) (sov x)
  | Macro (path, repl) ->
      Printf.sprintf "macro %s %s" path
        (String.concat ", "
           (List.map
              (fun (f, f') -> Printf.sprintf "%s/%s" (sof f) (sof f'))
              repl))
  | Mode mode -> Printf.sprintf "mode %s" (string_of_mode mode)
  | _ -> ""

let string_of_cmd =
  gen_string_of_cmd LK.string_of_sequent LK.string_of_formula LK.string_of_term
    LK.string_of_var

let ascii_string_of_cmd =
  gen_string_of_cmd LK.ascii_string_of_sequent LK.ascii_string_of_formula
    LK.ascii_string_of_term LK.ascii_string_of_var
