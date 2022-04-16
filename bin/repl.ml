open Lib

let ( let* ) = Result.bind

let parse_cmd line =
  let lexbuf = Sedlexing.Utf8.from_string line in
  try
    let lexer = Sedlexing.with_tokenizer Lexer.token lexbuf in
    let cmd =
      MenhirLib.Convert.Simplified.traditional2revised Parser.start_cmd lexer
    in
    Ok cmd
  with
  | Lexer.Error msg -> Error (Printf.sprintf "lexer error: %s" msg)
  | Parser.Error ->
      Error
        (Printf.sprintf "At offset %d: syntax error.\n%!"
           (Sedlexing.lexeme_start lexbuf))

let with_replacements repl =
  let open Cmd in
  function
  | Axiom f -> Axiom (f |> LK.with_replacements repl)
  | Premise (ant, suc) ->
      Premise
        ( List.map (LK.with_replacements repl) ant,
          List.map (LK.with_replacements repl) suc )
  | Weakening (side, i, f) -> Weakening (side, i, f |> LK.with_replacements repl)
  | ConjLeft (side, i, f) -> ConjLeft (side, i, f |> LK.with_replacements repl)
  | DisjRight (side, i, f) -> DisjRight (side, i, f |> LK.with_replacements repl)
  | Macro (name, repl') ->
      Macro
        ( name,
          List.map
            (fun (f, g) ->
              (f |> LK.with_replacements repl', g |> LK.with_replacements repl'))
            repl )
  | other -> other

let validate_sequent = function
  | Cmd.Classic -> LK.validate_sequent
  | Cmd.Intuitionistic -> LJ.validate_sequent

let rec process line mode proof =
  let* cmd = parse_cmd line in
  let* mode, proof, endsequent = handle_cmd mode proof cmd in
  let* _ = (validate_sequent mode) endsequent in
  Ok (mode, proof)

and handle_cmd mode proof cmd =
  match cmd with
  | Axiom a ->
      let s = ([ a ], [ a ]) in
      let* _ = (validate_sequent mode) s in
      let index, proof = proof |> Proof.add s (LK.Axiom a) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Premise s ->
      let* _ = (validate_sequent mode) s in
      let index, proof = proof |> Proof.add s (LK.Premise s) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Weakening (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = proof |> Proof.resolve index in
      let s =
        match side with
        | LK.Left -> (d :: ant, suc)
        | LK.Right -> (ant, suc @ [ d ])
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.Weakening (side, (ant, suc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Contraction (side, index) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match (side, ant, List.rev suc) with
        | LK.Left, d :: d' :: _, _ when d = d' -> Ok (List.tl ant, suc)
        | LK.Right, _, d :: d' :: _ when d = d' ->
            Ok (ant, List.rev (List.tl (List.rev suc)))
        | LK.Left, _ :: _ :: _, _ ->
            Error
              "contraction: the first two sequents of the antecedent must be \
               the same"
        | LK.Right, _, _ :: _ :: _ ->
            Error
              "contraction: the last two sequents of the succedent must be the \
               same"
        | LK.Left, _, _ ->
            Error "contraction: not enough formulas in the left sequent"
        | LK.Right, _, _ ->
            Error "contraction: not enough formulas in the right sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.Contraction (side, (ant, suc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Exchange (side, index, start) ->
      let* ant, suc = proof |> Proof.resolve index in
      if side = LK.Left && start + 1 >= List.length ant then
        Error "exchange: initial formula out of bounds"
      else if side = LK.Right && start + 1 >= List.length suc then
        Error "exchange: initial formula out of bounds"
      else
        let rec exch i = function
          | c :: d :: xs when i = start -> d :: c :: xs
          | x :: xs -> x :: exch (i + 1) xs
          | [] -> []
        in
        let* s =
          match (side, ant, suc) with
          | LK.Left, [ _ ], _ ->
              Error "exchange: not enough formulas in the left sequent"
          | LK.Left, [], _ ->
              Error "exchange: not enough formulas in the left sequent"
          | LK.Right, _, [ _ ] ->
              Error "exchange: not enough formulas in the right sequent"
          | LK.Right, _, [] ->
              Error "exchange: not enough formulas in the right sequent"
          | LK.Left, _, _ -> Ok (exch 0 ant, suc)
          | LK.Right, _, _ -> Ok (ant, exch 0 suc)
        in
        let* _ = (validate_sequent mode) s in
        let index, proof =
          proof |> Proof.add s (LK.Exchange (side, (ant, suc), start)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (mode, proof, s)
  | Cut (lindex, rindex) ->
      let* lant, lsuc = proof |> Proof.resolve lindex in
      let* rant, rsuc = proof |> Proof.resolve rindex in
      let* s =
        match (List.rev lsuc, rant) with
        | d :: _, d' :: _ when d = d' ->
            Ok (lant @ List.tl rant, List.rev (List.tl (List.rev lsuc)) @ rsuc)
        | _ :: _, _ :: _ ->
            Error
              "cut: last formula in left sequent must be equal to first \
               formula in right sequent"
        | _, [] -> Error "cut: not enough formulas in the right sequent"
        | [], _ -> Error "cut: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.Cut ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Negation (side, index) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match (side, ant, List.rev suc) with
        | LK.Left, _, d :: _ ->
            Ok (LK.Neg d :: ant, List.rev (List.tl (List.rev suc)))
        | LK.Right, d :: _, _ -> Ok (List.tl ant, suc @ [ LK.Neg d ])
        | LK.Left, _, _ ->
            Error "negation: not enough formulas in the right sequent"
        | LK.Right, _, _ ->
            Error "negation: not enough formulas in the left sequent"
      in
      let index, proof =
        proof |> Proof.add s (LK.NegIntro (side, (ant, suc))) cmd
      in
      let* _ = (validate_sequent mode) s in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ConjLeft (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match (side, ant) with
        | LK.Left, c :: _ -> Ok (LK.Conj (d, c) :: List.tl ant, suc)
        | LK.Right, c :: _ -> Ok (LK.Conj (c, d) :: List.tl ant, suc)
        | _, [] -> Error "lconj: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.ConjLeft (side, (ant, suc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ConjRight (lindex, rindex) ->
      let* lant, lsuc = proof |> Proof.resolve lindex in
      let* rant, rsuc = proof |> Proof.resolve rindex in
      let* s =
        if lant = rant then
          match (List.rev lsuc, List.rev rsuc) with
          | c :: delta, d :: delta' when delta = delta' ->
              Ok (lant, List.rev (LK.Conj (c, d) :: delta))
          | _ :: _, _ :: _ -> Error "rconj: succedents must share equal prefix"
          | _, [] -> Error "rconj: not enough formulas in the right sequent"
          | [], _ -> Error "rconj: not enough formulas in the left sequent"
        else Error "rconj: antecedents must be equal"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.ConjRight ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | DisjLeft (lindex, rindex) ->
      let* lant, lsuc = proof |> Proof.resolve lindex in
      let* rant, rsuc = proof |> Proof.resolve rindex in
      let* s =
        if lsuc = rsuc then
          match (lant, rant) with
          | c :: gamma, d :: gamma' when gamma = gamma' ->
              Ok (LK.Disj (c, d) :: gamma, lsuc)
          | _ :: _, _ :: _ -> Error "ldisj: succedents must share equal prefix"
          | _, [] -> Error "ldisj: not enough formulas in the right sequent"
          | [], _ -> Error "ldisj: not enough formulas in the left sequent"
        else Error "ldisj: succedents must be equal"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.DisjLeft ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | DisjRight (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match (side, List.rev suc) with
        | LK.Left, c :: _ ->
            Ok (ant, List.rev (LK.Disj (d, c) :: List.tl (List.rev suc)))
        | LK.Right, c :: _ ->
            Ok (ant, List.rev (LK.Disj (c, d) :: List.tl (List.rev suc)))
        | _, [] -> Error "rdisj: not enough formulas in the right sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.DisjRight (side, (ant, suc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ImplLeft (lindex, rindex) ->
      let* lant, lsuc = proof |> Proof.resolve lindex in
      let* rant, rsuc = proof |> Proof.resolve rindex in
      let* s =
        match (List.rev lsuc, rant) with
        | c :: delta, d :: pi ->
            Ok ((LK.Impl (c, d) :: lant) @ pi, List.rev delta @ rsuc)
        | _, [] -> Error "limpl: not enough formulas in the right sequent"
        | [], _ -> Error "limpl: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.ImplLeft ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ImplRight index ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match (ant, List.rev suc) with
        | c :: gamma, d :: delta ->
            Ok (gamma, List.rev (LK.Impl (c, d) :: delta))
        | _, [] -> Error "rimpl: not enough formulas in the right sequent"
        | [], _ -> Error "rimpl: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof = proof |> Proof.add s (LK.ImplRight (ant, suc)) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ForAllLeft (index, t, x) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match ant with
        | f :: gamma ->
            let f' = LK.ForAll (x, LK.substitute_term f t (LK.Var x)) in
            let* _ = LK.validate_formula f' in
            Ok (f' :: gamma, suc)
        | [] -> Error "lforall: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.ForAllLeft ((ant, suc), t, x)) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | ForAllRight (index, a, x) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match List.rev suc with
        | f :: delta ->
            let f' =
              LK.ForAll (x, LK.substitute_term f (LK.Var a) (LK.Var x))
            in
            Ok (ant, List.rev (f' :: delta))
        | [] -> Error "rforall: not enough formulas in the right sequent"
      in
      let* vs = (validate_sequent mode) s in
      if LK.VarSet.mem a vs then
        Error
          (Printf.sprintf
             "rforall: free variable %s cannot appear in lower sequent"
             (LK.string_of_var a))
      else
        let index, proof =
          proof |> Proof.add s (LK.ForAllRight ((ant, suc), a, x)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (mode, proof, s)
  | ExistsLeft (index, a, x) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match ant with
        | f :: gamma ->
            let f' =
              LK.Exists (x, LK.substitute_term f (LK.Var a) (LK.Var x))
            in
            Ok (f' :: gamma, suc)
        | [] -> Error "rforall: not enough formulas in the right sequent"
      in
      let* vs = (validate_sequent mode) s in
      if LK.VarSet.mem a vs then
        Error
          (Printf.sprintf
             "lexists: free variable %s cannot appear in lower sequent"
             (LK.string_of_var a))
      else
        let index, proof =
          proof |> Proof.add s (LK.ExistsLeft ((ant, suc), a, x)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (mode, proof, s)
  | ExistsRight (index, t, x) ->
      let* ant, suc = proof |> Proof.resolve index in
      let* s =
        match List.rev suc with
        | f :: delta ->
            let f' = LK.Exists (x, LK.substitute_term f t (LK.Var x)) in
            let* _ = LK.validate_formula f' in
            Ok (ant, List.rev (f' :: delta))
        | [] -> Error "rexists: not enough formulas in the left sequent"
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.ExistsRight ((ant, suc), t, x)) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Macro (path, repl) ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_in path in
      let rec aux mode proof =
        try
          let line = input_line ch in
          let* cmd = parse_cmd line in
          let* mode, proof, _ =
            handle_cmd mode proof (cmd |> with_replacements repl)
          in
          aux mode proof
        with End_of_file -> Ok (mode, proof)
      in
      let proof' = Proof.empty in
      let* _, proof' = aux mode proof' in
      let axioms, s = Proof.axioms_and_endsequent proof' in
      let filename = List.hd (List.rev (String.split_on_char '/' path)) in
      let name =
        String.concat "."
          (List.rev (List.tl (List.rev (String.split_on_char '.' filename))))
      in
      let* _ = (validate_sequent mode) s in
      let index, proof =
        proof |> Proof.add s (LK.Macro (name, repl, axioms)) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (mode, proof, s)
  | Print ->
      Proof.print_proof proof;
      Ok (mode, proof, LK.empty_sequent)
  | TeX path ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_out path in
      Printf.fprintf ch "\\begin{prooftree}\n%s\n\\end{prooftree}\n"
        (Proof.tex_of_proof proof);
      close_out ch;
      Ok (mode, proof, LK.empty_sequent)
  | Load path ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_in path in
      let rec aux mode proof =
        try
          let line = input_line ch in
          match process line mode proof with
          | Ok (mode, proof) -> aux mode proof
          | err -> err
        with End_of_file -> Ok (mode, proof)
      in
      let* mode, proof = aux mode proof in
      Ok (mode, proof, LK.empty_sequent)
  | Save path ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_out path in
      Printf.fprintf ch "%s" (Proof.string_of_proof_cmds proof);
      close_out ch;
      Ok (mode, proof, LK.empty_sequent)
  | Clear -> Ok (Cmd.Classic, Proof.empty, LK.empty_sequent)
  | Mode mode' ->
      if not (mode = mode') then
        Printf.printf "  mode switched from %s to %s. Proof cleared.\n"
          (Cmd.string_of_mode mode) (Cmd.string_of_mode mode');
      Ok (mode', Proof.empty, LK.empty_sequent)
  | Nop -> Ok (mode, proof, LK.empty_sequent)
  | CutElim -> Ok (mode, Proof.cut_elimination proof, LK.empty_sequent)
  | ReductionTree s ->
      let rt = ReductionTree.reduction_tree s in
      Printf.printf "%s\n%!" (ReductionTree.tex_of_tree rt);
      Ok (mode, proof, LK.empty_sequent)

let rec loop channel mode proof =
  Printf.printf "> %!";
  let line = input_line channel in
  match process line mode proof with
  | Ok (mode, proof) -> loop channel mode proof
  | Error err ->
      let () = Printf.printf "error: %s\n" err in
      loop channel mode proof

let () = loop stdin Cmd.Classic Proof.empty
