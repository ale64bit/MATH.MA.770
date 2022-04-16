type var = Free of string | Bound of string

type term =
  | Const of string
  | Var of var
  | Fun of string * term list
  | Term of string * term list

type formula =
  | Atom of string * term list
  | Neg of formula
  | Disj of formula * formula
  | Conj of formula * formula
  | Impl of formula * formula
  | Exists of var * formula
  | ForAll of var * formula
  | Formula of string * term list

type cedent = formula list
type sequent = cedent * cedent
type side = Left | Right

type inference =
  | Premise of sequent
  | Axiom of formula
  | Weakening of side * sequent
  | Contraction of side * sequent
  | Exchange of side * sequent * int
  | Cut of sequent * sequent
  | Mix of sequent * sequent * formula
  | NegIntro of side * sequent
  | ConjLeft of side * sequent
  | ConjRight of sequent * sequent
  | DisjLeft of sequent * sequent
  | DisjRight of side * sequent
  | ImplLeft of sequent * sequent
  | ImplRight of sequent
  | ForAllLeft of sequent * term * var
  | ForAllRight of sequent * var * var
  | ExistsLeft of sequent * var * var
  | ExistsRight of sequent * term * var
  | Macro of string * (formula * formula) list * sequent list

type assignment = var -> bool
type 'a interpretation = term -> assignment -> 'a

val empty_sequent : sequent
val antecedent : sequent -> cedent
val succedent : sequent -> cedent

(* Convert to human-readable string *)
val string_of_side : side -> string
val string_of_var : var -> string
val string_of_term : term -> string
val string_of_formula : formula -> string
val string_of_sequent : sequent -> string

(* Convert to ASCII string *)
val ascii_string_of_var : var -> string
val ascii_string_of_term : term -> string
val ascii_string_of_formula : formula -> string
val ascii_string_of_sequent : sequent -> string

(* Convert to TeX *)
val tex_of_var : var -> string
val tex_of_term : term -> string
val tex_of_formula : formula -> string
val tex_of_sequent : sequent -> string

(* A set of variables *)
module VarSet : Set.S with type elt = var

(* A set of formulas *)
module FormulaSet : Set.S with type elt = formula

val substitute_term : formula -> term -> term -> formula
val validate_formula : formula -> (VarSet.t, string) result
val validate_sequent : sequent -> (VarSet.t, string) result
val valid_inference : inference -> sequent -> bool
val with_replacements : (formula * formula) list -> formula -> formula
