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

let axioms_and_endsequent proof =
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  let axioms =
    List.filter_map
      (fun (s, { ent_derivation; _ }) ->
        match ent_derivation with
        | Axiom _ -> Some [ s ]
        | Macro (_, _, axioms) -> Some axioms
        | _ -> None)
      entries
  in
  let endseq, _ = List.hd (List.rev entries) in
  (List.sort_uniq Stdlib.compare (List.concat axioms), endseq)

let string_of_derivation proof =
  let open LK in
  let open SequentMap in
  function
  | Axiom _ -> "[Axiom]"
  | Premise _ -> "[Premise]"
  | Weakening (side, s) ->
      Printf.sprintf "[W%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Contraction (side, s) ->
      Printf.sprintf "[C%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Exchange (side, s, _) ->
      Printf.sprintf "[E%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Cut (s, t) ->
      Printf.sprintf "[Cut (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
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
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  List.iteri
    (fun i (s, { ent_derivation; _ }) ->
      Printf.printf "  (%d) %-60s%s\n" (i + 1) (LK.string_of_sequent s)
        (string_of_derivation proof ent_derivation))
    entries

let tex_of_proof proof =
  let open LK in
  let rec aux s =
    match (SequentMap.find s proof).ent_derivation with
    | Axiom f -> Printf.sprintf "\\AxiomC{$%s$}" (tex_of_sequent ([ f ], [ f ]))
    | Premise s -> Printf.sprintf "\\AxiomC{[$%s$]}" (tex_of_sequent s)
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
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ej.ent_index ei.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  let s, _ = List.hd entries in
  aux s

let string_of_proof_cmds proof =
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  String.concat "\n"
    (List.map
       (fun (_, { ent_command; _ }) -> Cmd.ascii_string_of_cmd ent_command)
       entries)
