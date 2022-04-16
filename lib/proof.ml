(* A proof is stored as a Map of sequents to their entries *)
module SequentMap = Map.Make (struct
  type t = LK.sequent

  let compare = Stdlib.compare
end)

(* Metadata about a sequent in a proof *)
type entry = {
  ent_index : int;
  ent_command : Cmd.cmd;
  ent_derivation : LK.inference;
}

type proof = entry SequentMap.t

let empty = SequentMap.empty

(* Add a sequent to the proof along with its inference *)
let add s inf cmd proof =
  assert (LK.valid_inference inf s);
  if SequentMap.mem s proof then ((SequentMap.find s proof).ent_index, proof)
  else
    let index = SequentMap.cardinal proof + 1 in
    ( index,
      proof
      |> SequentMap.add s
           { ent_index = index; ent_command = cmd; ent_derivation = inf } )

let resolve index proof =
  match
    List.find_opt
      (fun (_, { ent_index; _ }) -> ent_index = index)
      (List.of_seq (SequentMap.to_seq proof))
  with
  | Some (s, _) -> Ok s
  | None -> Error (Printf.sprintf "no sequent with index %d" index)

let proof_entries proof =
  List.sort
    (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
    (SequentMap.bindings proof)

let proof_axioms proof =
  let axioms =
    List.filter_map
      (fun (s, { ent_derivation; _ }) ->
        match ent_derivation with
        | Axiom _ -> Some [ s ]
        | Macro (_, _, axioms) -> Some axioms
        | _ -> None)
      (proof_entries proof)
  in
  List.sort_uniq Stdlib.compare (List.concat axioms)

let endsequent proof =
  let entries = proof_entries proof in
  let endseq, _ = List.hd (List.rev entries) in
  endseq

let axioms_and_endsequent proof = (proof_axioms proof, endsequent proof)

let expand_antecedent s s' proof =
  let open LK in
  let module S = FormulaSet in
  let cs = S.of_list (antecedent s) in
  let cs' = S.of_list (antecedent s') in
  assert (S.subset cs cs');
  let missing = S.diff cs' cs in
  let proof, c =
    S.fold
      (fun a (p, c) ->
        let _, p =
          add (a :: c, succedent s) (Weakening (Left, (c, succedent s))) Nop p
        in
        (p, a :: c))
      missing
      (proof, antecedent s)
  in
  (proof, (c, succedent s))

let expand_succedent s s' proof =
  let open LK in
  let module S = FormulaSet in
  let cs = S.of_list (succedent s) in
  let cs' = S.of_list (succedent s') in
  assert (S.subset cs cs');
  let missing = S.diff cs' cs in
  let proof, c =
    S.fold
      (fun a (p, c) ->
        let _, p =
          add
            (antecedent s, c @ [ a ])
            (Weakening (Right, (antecedent s, c)))
            Nop p
        in
        (p, c @ [ a ]))
      missing
      (proof, succedent s)
  in
  (proof, (antecedent s, c))

let sort_antecedent s s' proof =
  let open LK in
  let module S = FormulaSet in
  assert (List.length (antecedent s) = List.length (antecedent s'));
  assert (S.equal (S.of_list (antecedent s)) (S.of_list (antecedent s')));
  let rec aux i acc t t' p =
    match (t, t') with
    | [], [] -> p
    | a :: xs, a' :: ys when a = a' -> aux (i + 1) (a :: acc) xs ys p
    | _ :: xs, a' :: _ ->
        let j, _ =
          List.find (fun (_, b) -> a' = b) (List.mapi (fun i a -> (i, a)) xs)
        in
        let _, p =
          add
            (List.rev acc @ ListUtil.exch j t, succedent s)
            (Exchange (Left, (List.rev acc @ t, succedent s), i + j))
            Nop p
        in
        aux i acc (ListUtil.exch j t) t' p
    | _ -> failwith "cannot happen"
  in
  (aux 0 [] (antecedent s) (antecedent s') proof, (antecedent s', succedent s))

let sort_succedent s s' proof =
  let open LK in
  let module S = FormulaSet in
  assert (List.length (succedent s) = List.length (succedent s'));
  assert (S.equal (S.of_list (succedent s)) (S.of_list (succedent s')));
  let rec aux i acc t t' p =
    match (t, t') with
    | [], [] -> p
    | a :: xs, a' :: ys when a = a' -> aux (i + 1) (a :: acc) xs ys p
    | _ :: xs, a' :: _ ->
        let j, _ =
          List.find (fun (_, b) -> a' = b) (List.mapi (fun i a -> (i, a)) xs)
        in
        let _, p =
          add
            (antecedent s, List.rev acc @ ListUtil.exch j t)
            (Exchange (Right, (antecedent s, List.rev acc @ t), i + j))
            Nop p
        in
        aux i acc (ListUtil.exch j t) t' p
    | _ -> failwith "cannot happen"
  in
  (aux 0 [] (succedent s) (succedent s') proof, (antecedent s, succedent s'))

let expand_and_sort_sequent s s' proof =
  let open LK in
  let module S = FormulaSet in
  assert (List.length (antecedent s) <= List.length (antecedent s'));
  assert (List.length (succedent s) <= List.length (succedent s'));
  assert (S.subset (S.of_list (antecedent s)) (S.of_list (antecedent s')));
  assert (S.subset (S.of_list (succedent s)) (S.of_list (succedent s')));
  let proof, s = expand_antecedent s s' proof in
  let proof, s = expand_succedent s s' proof in
  let proof, s = sort_antecedent s s' proof in
  let proof, s = sort_succedent s s' proof in
  assert (s = s');
  proof

(*
          Γ → Δ
    -----------------
    A, ... , A, Γ* → Δ
    -----------------
       A, Γ* → Δ
*)
(*
TODO
let drain_antecedent_left s a proof =
  let open LK in
  let sl, sr = List.partition (fun a' -> a' = a) (antecedent s) in
  let s' = (sl @ sr, succedent s) in
  let proof, _ = sort_antecedent s s' proof in
  let rec aux s proof =
    match s with
    | a' :: a'' :: gamma, delta when a = a' && a = a'' ->
        let s' = (a :: gamma, delta) in
        let _, p = add s' (Contraction (Left, s)) Nop proof in
        aux s' p
    | _ ->
        assert (s = (a :: sr, succedent s'));
        proof
  in
  aux s' proof
  *)

(*
  TODO:
    drain_antecedent_right s a proof
    drain_succedent_left s a proof
    drain_succedent_right s a proof
    regularize proof
    subproof s proof
    copy_with_replacement a t proof
    expand macros
*)

let convert_cut_to_mix proof =
  let open LK in
  let rec aux s p =
    match (SequentMap.find s proof).ent_derivation with
    | Premise _ as inf ->
        let _, p = add s inf Nop p in
        p
    | Axiom _ as inf ->
        let _, p = add s inf Nop p in
        p
    | Weakening (_, s1) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | Contraction (_, s1) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | Exchange (_, s1, _) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | Cut (s1, s2) ->
        let d = List.hd (antecedent s2) in
        let p = p |> aux s1 |> aux s2 in
        let s' =
          let not_d a = not (a = d) in
          ( antecedent s1 @ List.filter not_d (antecedent s2),
            List.filter not_d (succedent s1) @ succedent s2 )
        in
        let _, p = add s' (Mix (s1, s2, d)) Nop p in
        expand_and_sort_sequent s' s p
    | Mix (s1, s2, _) as inf ->
        let p = aux s1 p in
        let p = aux s2 p in
        let _, p = add s inf Nop p in
        p
    | NegIntro (_, s1) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ConjLeft (_, s1) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ConjRight (s1, s2) as inf ->
        let p = aux s1 p in
        let p = aux s2 p in
        let _, p = add s inf Nop p in
        p
    | DisjLeft (s1, s2) as inf ->
        let p = aux s1 p in
        let p = aux s2 p in
        let _, p = add s inf Nop p in
        p
    | DisjRight (_, s1) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ImplLeft (s1, s2) as inf ->
        let p = aux s1 p in
        let p = aux s2 p in
        let _, p = add s inf Nop p in
        p
    | ImplRight s1 as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ForAllLeft (s1, _, _) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ForAllRight (s1, _, _) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ExistsLeft (s1, _, _) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | ExistsRight (s1, _, _) as inf ->
        let p = aux s1 p in
        let _, p = add s inf Nop p in
        p
    | Macro _ -> p
  in
  aux (endsequent proof) empty

let cut_elimination proof =
  let proof = convert_cut_to_mix proof in
  (* TODO continue *)
  proof

let string_of_derivation proof =
  let open LK in
  let open SequentMap in
  function
  | Premise _ -> "[Premise]"
  | Axiom _ -> "[Axiom]"
  | Weakening (side, s) ->
      Printf.sprintf "[W%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Contraction (side, s) ->
      Printf.sprintf "[C%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Exchange (side, s, _) ->
      Printf.sprintf "[E%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Cut (s, t) ->
      Printf.sprintf "[Cut (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | Mix (s, t, a) ->
      Printf.sprintf "[Mix (%d) (%d) (%s)]" (find s proof).ent_index
        (find t proof).ent_index (LK.string_of_formula a)
  | NegIntro (side, s) ->
      Printf.sprintf "[¬%s (%d)]" (string_of_side side) (find s proof).ent_index
  | ConjLeft (_, s) -> Printf.sprintf "[∧L (%d)]" (find s proof).ent_index
  | ConjRight (s, t) ->
      Printf.sprintf "[∧R (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | DisjLeft (s, t) ->
      Printf.sprintf "[∨L (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | DisjRight (_, s) -> Printf.sprintf "[∨R (%d)]" (find s proof).ent_index
  | ImplLeft (s, t) ->
      Printf.sprintf "[⊃L (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | ImplRight s -> Printf.sprintf "[⊃R (%d)]" (find s proof).ent_index
  | ForAllLeft (s, t, x) ->
      Printf.sprintf "[∀L (%d) %s -> %s]" (find s proof).ent_index
        (string_of_term t) (string_of_var x)
  | ForAllRight (s, a, x) ->
      Printf.sprintf "[∀R (%d) %s -> %s]" (find s proof).ent_index
        (string_of_var a) (string_of_var x)
  | ExistsLeft (s, a, x) ->
      Printf.sprintf "[∃L (%d) %s -> %s]" (find s proof).ent_index
        (string_of_var a) (string_of_var x)
  | ExistsRight (s, t, x) ->
      Printf.sprintf "[∃R (%d) %s -> %s]" (find s proof).ent_index
        (string_of_term t) (string_of_var x)
  | Macro (name, _, _) -> Printf.sprintf "[macro %s]" name

let print_proof proof =
  let entries = proof_entries proof in
  List.iteri
    (fun i (s, { ent_derivation; _ }) ->
      Printf.printf "  (%d) %-60s%s\n" (i + 1) (LK.string_of_sequent s)
        (string_of_derivation proof ent_derivation))
    entries

let tex_of_proof proof =
  let open LK in
  let rec aux s =
    match (SequentMap.find s proof).ent_derivation with
    | Premise s -> Printf.sprintf "\\AxiomC{[$%s$]}" (tex_of_sequent s)
    | Axiom f -> Printf.sprintf "\\AxiomC{$%s$}" (tex_of_sequent ([ f ], [ f ]))
    | Weakening (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[W%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Contraction (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[C%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Exchange (side, s', _) ->
        Printf.sprintf "%s\n\\RightLabel{[X%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Cut (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[Cut]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | Mix (sl, sr, a) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[Mix(%s)]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_formula a) (tex_of_sequent s)
    | NegIntro (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\neg$%s]}\n\\UnaryInfC{$%s$}"
          (aux s') (string_of_side side) (tex_of_sequent s)
    | ConjLeft (_, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\land$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ConjRight (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\land$R]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | DisjLeft (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\lor$L]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | DisjRight (_, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\lor$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ImplLeft (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\supset$L]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | ImplRight s' ->
        Printf.sprintf "%s\n\\RightLabel{[$\\supset$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ForAllLeft (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\forall$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ForAllRight (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\forall$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ExistsLeft (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\exists$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ExistsRight (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\exists$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | Macro (name, _, axioms) ->
        let nth_inf =
          [
            (1, "UnaryInfC");
            (2, "BinaryInfC");
            (3, "TrinaryInfC");
            (4, "QuaternaryInfC");
            (5, "QuinaryInfC");
          ]
        in
        let ss =
          String.concat "\n"
            (List.map
               (fun s -> Printf.sprintf "\\AxiomC{$%s$}" (tex_of_sequent s))
               axioms)
        in
        Printf.sprintf "%s\n\\doubleLine\n\\RightLabel{[%s]}\n\\%s{$%s$}" ss
          name
          (List.assoc (List.length axioms) nth_inf)
          (tex_of_sequent s)
  in
  aux (endsequent proof)

let string_of_proof_cmds proof =
  let entries = proof_entries proof in
  String.concat "\n"
    (List.map
       (fun (_, { ent_command; _ }) -> Cmd.ascii_string_of_cmd ent_command)
       entries)
