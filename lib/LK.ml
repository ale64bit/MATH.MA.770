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

type sequent = formula list * formula list
type side = Left | Right

type inference =
  | Axiom of formula
  | Premise of sequent
  | Weakening of side * sequent
  | Contraction of side * sequent
  | Exchange of side * sequent * int
  | Cut of sequent * sequent
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

let empty_sequent = ([], [])
let string_of_side = function Left -> "L" | Right -> "R"
let string_of_var = function Free a -> a | Bound x -> x

let rec string_of_term = function
  | Const k -> k
  | Var x -> string_of_var x
  | Fun (f, ts) ->
      let args = String.concat "," (List.map string_of_term ts) in
      Printf.sprintf "%s(%s)" f args
  | Term (t, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)"
              (String.concat "," (List.map string_of_term ts))
      in
      Printf.sprintf "%s%s" t args

let rec string_of_formula = function
  | Conj (Impl (a, b), Impl (b', a')) when a = a' && b = b' ->
      Printf.sprintf "(%s ≡ %s)" (string_of_formula a) (string_of_formula b)
  | Atom (r, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)"
              (String.concat "," (List.map string_of_term ts))
      in
      Printf.sprintf "%s%s" r args
  | Neg a -> Printf.sprintf "¬%s" (string_of_formula a)
  | Disj (a, b) ->
      Printf.sprintf "(%s ∨ %s)" (string_of_formula a) (string_of_formula b)
  | Conj (a, b) ->
      Printf.sprintf "(%s ∧ %s)" (string_of_formula a) (string_of_formula b)
  | Impl (a, b) ->
      Printf.sprintf "(%s ⊃ %s)" (string_of_formula a) (string_of_formula b)
  | Exists (x, a) ->
      Printf.sprintf "∃%s %s" (string_of_var x) (string_of_formula a)
  | ForAll (x, a) ->
      Printf.sprintf "∀%s %s" (string_of_var x) (string_of_formula a)
  | Formula (a, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)"
              (String.concat "," (List.map string_of_term ts))
      in
      Printf.sprintf "%s%s" a args

let string_of_sequent (antecedent, succedent) =
  Printf.sprintf "%s → %s"
    (String.concat ", " (List.map string_of_formula antecedent))
    (String.concat ", " (List.map string_of_formula succedent))

let ascii_string_of_var = string_of_var
let ascii_string_of_term = string_of_term

let rec ascii_string_of_formula = function
  | Atom (r, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)"
              (String.concat "," (List.map ascii_string_of_term ts))
      in
      Printf.sprintf "%s%s" r args
  | Neg a -> Printf.sprintf "~%s" (ascii_string_of_formula a)
  | Disj (a, b) ->
      Printf.sprintf "(%s | %s)"
        (ascii_string_of_formula a)
        (ascii_string_of_formula b)
  | Conj (a, b) ->
      Printf.sprintf "(%s & %s)"
        (ascii_string_of_formula a)
        (ascii_string_of_formula b)
  | Impl (a, b) ->
      Printf.sprintf "(%s => %s)"
        (ascii_string_of_formula a)
        (ascii_string_of_formula b)
  | Exists (x, a) ->
      Printf.sprintf ":E%s %s" (ascii_string_of_var x)
        (ascii_string_of_formula a)
  | ForAll (x, a) ->
      Printf.sprintf ":A%s %s" (ascii_string_of_var x)
        (ascii_string_of_formula a)
  | Formula (a, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)"
              (String.concat "," (List.map ascii_string_of_term ts))
      in
      Printf.sprintf "%s%s" a args

let ascii_string_of_sequent (antecedent, succedent) =
  Printf.sprintf "%s -> %s"
    (String.concat ", " (List.map ascii_string_of_formula antecedent))
    (String.concat ", " (List.map ascii_string_of_formula succedent))

let tex_of_var = string_of_var
let tex_of_term = string_of_term

let rec tex_of_formula = function
  | Conj (Impl (a, b), Impl (b', a')) when a = a' && b = b' ->
      Printf.sprintf "(%s \\equiv %s)" (tex_of_formula a) (tex_of_formula b)
  | Atom (r, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)" (String.concat "," (List.map tex_of_term ts))
      in
      Printf.sprintf "%s%s" r args
  | Neg a -> Printf.sprintf "\\neg %s" (tex_of_formula a)
  | Disj (a, b) ->
      Printf.sprintf "(%s \\lor %s)" (tex_of_formula a) (tex_of_formula b)
  | Conj (a, b) ->
      Printf.sprintf "(%s \\land %s)" (tex_of_formula a) (tex_of_formula b)
  | Impl (a, b) ->
      Printf.sprintf "(%s \\supset %s)" (tex_of_formula a) (tex_of_formula b)
  | Exists (x, a) ->
      Printf.sprintf "\\exists %s %s" (tex_of_var x) (tex_of_formula a)
  | ForAll (x, a) ->
      Printf.sprintf "\\forall %s %s" (tex_of_var x) (tex_of_formula a)
  | Formula (a, ts) ->
      let args =
        match ts with
        | [] -> ""
        | _ ->
            Printf.sprintf "(%s)" (String.concat "," (List.map tex_of_term ts))
      in
      Printf.sprintf "%s%s" a args

let tex_of_sequent (antecedent, succedent) =
  Printf.sprintf "%s \\rightarrow %s"
    (String.concat ", " (List.map tex_of_formula antecedent))
    (String.concat ", " (List.map tex_of_formula succedent))

module VarSet = Set.Make (struct
  type t = var

  let compare = Stdlib.compare
end)

let substitute_term f s t =
  let rec aux_term = function
    | s' when s = s' -> t
    | Fun (f, ss) -> Fun (f, List.map aux_term ss)
    | Term (s, ss) -> Term (s, List.map aux_term ss)
    | s' -> s'
  in
  let rec aux_formula = function
    | Atom (r, ss) -> Atom (r, List.map aux_term ss)
    | Neg a -> Neg (aux_formula a)
    | Disj (a, b) -> Disj (aux_formula a, aux_formula b)
    | Conj (a, b) -> Conj (aux_formula a, aux_formula b)
    | Impl (a, b) -> Impl (aux_formula a, aux_formula b)
    | Exists (x, a) -> Exists (x, aux_formula a)
    | ForAll (x, a) -> ForAll (x, aux_formula a)
    | Formula (a, ts) -> Formula (a, List.map aux_term ts)
  in
  aux_formula f

let ( let* ) = Result.bind

let validate_formula a =
  let open VarSet in
  let rec aux_term = function
    | Const _ -> empty
    | Var v -> singleton v
    | Fun (_, ts) ->
        List.fold_left (fun acc t -> union acc (aux_term t)) empty ts
    | Term (_, ts) ->
        List.fold_left (fun acc t -> union acc (aux_term t)) empty ts
  and aux_quantifier bound x a =
    if mem x bound then
      Error
        (Printf.sprintf
           "bound variable %s cannot be rebound inside a where it was \
            previously bound"
           (string_of_var x))
    else
      let* va = aux (add x bound) a in
      if not (mem x va) then
        Error
          (Printf.sprintf "bound variable %s must occur in its scope"
             (string_of_var x))
      else Ok (remove x va)
  and aux bound = function
    | Atom (_, ts) ->
        Ok (List.fold_left (fun acc t -> union acc (aux_term t)) empty ts)
    | Neg a -> aux bound a
    | Disj (a, b) ->
        let* va = aux bound a in
        let* vb = aux bound b in
        Ok (union va vb)
    | Conj (a, b) ->
        let* va = aux bound a in
        let* vb = aux bound b in
        Ok (union va vb)
    | Impl (a, b) ->
        let* va = aux bound a in
        let* vb = aux bound b in
        Ok (union va vb)
    | Exists (x, a) -> aux_quantifier bound x a
    | ForAll (x, a) -> aux_quantifier bound x a
    | Formula (_, ts) ->
        Ok (List.fold_left (fun acc t -> union acc (aux_term t)) empty ts)
  in
  let* va = aux empty a in
  match find_first_opt (function Free _ -> false | Bound _ -> true) va with
  | Some x ->
      Error
        (Printf.sprintf "bound variable %s does not have an outer quantifer"
           (string_of_var x))
  | None -> Ok va

let validate_sequent (ant, suc) =
  let open VarSet in
  let* vs =
    List.fold_left
      (fun vs f ->
        let* vs = vs in
        let* vf = validate_formula f in
        Ok (union vs vf))
      (Ok empty) (ant @ suc)
  in
  Ok vs

let rec with_replacements repl f =
  match List.assoc_opt f repl with
  | Some f' -> f'
  | None -> (
      match f with
      | Neg f -> Neg (f |> with_replacements repl)
      | Disj (f, g) ->
          Disj (f |> with_replacements repl, g |> with_replacements repl)
      | Conj (f, g) ->
          Conj (f |> with_replacements repl, g |> with_replacements repl)
      | Impl (f, g) ->
          Impl (f |> with_replacements repl, g |> with_replacements repl)
      | Exists (x, f) -> Exists (x, f |> with_replacements repl)
      | ForAll (x, f) -> ForAll (x, f |> with_replacements repl)
      | other -> other)
