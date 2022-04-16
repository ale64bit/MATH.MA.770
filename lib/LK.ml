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

let empty_sequent = ([], [])
let antecedent (ant, _) = ant
let succedent (_, suc) = suc
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
      Printf.sprintf "%s%s"
        (Str.global_replace (Str.regexp_string "*") "^*" a)
        args

let tex_of_sequent (antecedent, succedent) =
  Printf.sprintf "%s \\rightarrow %s"
    (String.concat ", " (List.map tex_of_formula antecedent))
    (String.concat ", " (List.map tex_of_formula succedent))

module VarSet = Set.Make (struct
  type t = var

  let compare = Stdlib.compare
end)

module FormulaSet = Set.Make (struct
  type t = formula

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

let rec is_subterm_of_term t = function
  | Const _ as t' -> t = t'
  | Var _ as t' -> t = t'
  | Fun (_, ts) as t' -> t = t' || List.exists (is_subterm_of_term t) ts
  | Term (_, ts) as t' -> t = t' || List.exists (is_subterm_of_term t) ts

let rec is_subterm_of_formula t = function
  | Atom (_, ts) -> List.exists (is_subterm_of_term t) ts
  | Neg a -> is_subterm_of_formula t a
  | Disj (a, b) -> is_subterm_of_formula t a || is_subterm_of_formula t b
  | Conj (a, b) -> is_subterm_of_formula t a || is_subterm_of_formula t b
  | Impl (a, b) -> is_subterm_of_formula t a || is_subterm_of_formula t b
  | Exists (_, a) -> is_subterm_of_formula t a
  | ForAll (_, a) -> is_subterm_of_formula t a
  | Formula (_, ts) -> List.exists (is_subterm_of_term t) ts

let valid_inference inf s =
  let open List in
  let open ListUtil in
  match (inf, s) with
  | Premise s, s' when s = s' -> true
  | Axiom a, ([ a' ], [ a'' ]) when a = a' && a = a'' -> true
  | Weakening (Left, (gamma, delta)), (_ :: gamma', delta')
    when gamma = gamma' && delta = delta' ->
      true
  | Weakening (Right, (gamma, delta)), (gamma', delta')
    when gamma = gamma' && delta = revtl delta' ->
      true
  | Contraction (Left, (d :: d' :: gamma, delta)), (d'' :: gamma', delta')
    when d = d' && d = d'' && gamma = gamma' && delta = delta' ->
      true
  | Contraction (Right, (gamma, delta)), (gamma', delta')
    when gamma = gamma' && rev delta = hd (rev delta) :: rev delta' ->
      true
  | Exchange (Left, (gamma, delta), i), (gamma', delta')
    when exch i gamma = gamma' && delta = delta' ->
      true
  | Exchange (Right, (gamma, delta), i), (gamma', delta')
    when gamma = gamma' && exch i delta = delta' ->
      true
  | Cut ((gamma, delta), (pi, lambda)), (gamma', delta')
    when revhd delta = hd pi
         && gamma @ tl pi = gamma'
         && revtl delta @ lambda = delta' ->
      true
  | Mix ((gamma, delta), (pi, lambda), a), (gamma', delta')
    when gamma @ filter (fun a' -> not (a' = a)) pi = gamma'
         && filter (fun a' -> not (a' = a)) delta @ lambda = delta' ->
      true
  | NegIntro (Left, (gamma, delta)), (gamma', delta')
    when Neg (revhd delta) :: gamma = gamma' && revtl delta = delta' ->
      true
  | NegIntro (Right, (gamma, delta)), (gamma', delta')
    when tl gamma = gamma' && delta @ [ Neg (hd gamma) ] = delta' ->
      true
  | ConjLeft (Left, (c :: gamma, delta)), (Conj (_, c') :: gamma', delta')
    when c = c' && gamma = gamma' && delta = delta' ->
      true
  | ConjLeft (Right, (c :: gamma, delta)), (Conj (c', _) :: gamma', delta')
    when c = c' && gamma = gamma' && delta = delta' ->
      true
  | ConjRight ((gamma, delta), (pi, lambda)), (gamma', delta')
    when gamma = pi
         && revtl delta = revtl lambda
         && gamma = gamma'
         && revtl delta @ [ Conj (revhd delta, revhd lambda) ] = delta' ->
      true
  | DisjLeft ((c :: gamma, delta), (d :: pi, lambda)), (gamma', delta')
    when gamma = pi && delta = lambda
         && Disj (c, d) :: gamma = gamma'
         && delta = delta' ->
      true
  | DisjRight (Left, (gamma, delta)), (gamma', delta') when gamma = gamma' -> (
      match (rev delta, rev delta') with
      | c :: s, Disj (_, c') :: s' when c = c' && s = s' -> true
      | _ -> false)
  | DisjRight (Right, (gamma, delta)), (gamma', delta') when gamma = gamma' -> (
      match (rev delta, rev delta') with
      | c :: s, Disj (c', _) :: s' when c = c' && s = s' -> true
      | _ -> false)
  | ImplLeft ((gamma, delta), (d :: pi, lambda)), (gamma', delta')
    when (Impl (revhd delta, d) :: gamma) @ pi = gamma'
         && revtl delta @ lambda = delta' ->
      true
  | ImplRight (c :: gamma, delta), (gamma', delta')
    when gamma = gamma' && revtl delta @ [ Impl (c, revhd delta) ] = delta' ->
      true
  | ForAllLeft ((f :: gamma, delta), t, (Bound _ as x)), (gamma', delta')
    when ForAll (x, substitute_term f t (Var x)) :: gamma = gamma'
         && delta = delta' ->
      true
  | ForAllRight ((gamma, delta), (Free _ as a), (Bound _ as x)), (gamma', delta')
    when gamma = gamma'
         && revtl delta
            @ [ ForAll (x, substitute_term (revhd delta) (Var a) (Var x)) ]
            = delta'
         && List.for_all (fun f -> not (is_subterm_of_formula (Var a) f)) gamma
         && List.for_all
              (fun f -> not (is_subterm_of_formula (Var a) f))
              (revtl delta) ->
      true
  | ( ExistsLeft ((f :: gamma, delta), (Free _ as a), (Bound _ as x)),
      (gamma', delta') )
    when Exists (x, substitute_term f (Var x) (Var x)) :: gamma = gamma'
         && delta = delta'
         && List.for_all (fun f -> not (is_subterm_of_formula (Var a) f)) gamma
         && List.for_all (fun f -> not (is_subterm_of_formula (Var a) f)) delta
    ->
      true
  | ExistsRight ((gamma, delta), t, (Bound _ as x)), (gamma', delta')
    when gamma = gamma'
         && revtl delta
            @ [ Exists (x, substitute_term (revhd delta) t (Var x)) ]
            = delta' ->
      true
  | Macro _, _ -> true
  | _ -> false
