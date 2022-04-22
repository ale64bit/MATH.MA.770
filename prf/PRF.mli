(* Variable names *)
type var = string

(* Function application *)
type app = string * var list

(* A Primitive-Recursive Function definition step *)
type t =
  | Succ of string * var list * var
  | Const of string * var list * Nat.t
  | Id of string * var list * var
  | Subs of string * var list * string * app list
  | Ind0 of {
      ind0_base_f : string;
      ind0_base_zero : Nat.t;
      ind0_base_q : Nat.t;
      ind0_step_f : string;
      ind0_step_y' : string;
      ind0_step_xi : string;
      ind0_step_y : string;
      ind0_step_app : app;
    }
  | Ind1 of {
      ind1_base_f : string;
      ind1_base_zero : Nat.t;
      ind1_base_xs : var list;
      ind1_base_psi : app;
      ind1_step_f : string;
      ind1_step_y' : string;
      ind1_step_xs : var list;
      ind1_step_xi : string;
      ind1_step_y : string;
      ind1_step_app : app;
      ind1_step_args : var list;
    }

val is_valid : t -> bool

(* Evaluates a PRF for the given arguments. *)
val eval : t list -> string -> Nat.t list -> (Nat.t, string) result
