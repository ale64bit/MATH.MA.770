type node_formula = NonReduced of LK.formula | Reduced of LK.formula
type node_sequent = node_formula list * node_formula list
type node = { nod_stage : int; nod_children : node_sequent list }

module FormulaMap = Map.Make (struct
  type t = LK.formula

  let compare = Stdlib.compare
end)

module SequentMap = Map.Make (struct
  type t = node_sequent

  let compare = Stdlib.compare
end)

type t = node SequentMap.t

let lift_formula a = NonReduced a

let lift_sequent (gamma, delta) =
  (List.map lift_formula gamma, List.map lift_formula delta)

let unlift_formula = function NonReduced a -> a | Reduced a -> a

let unlift_sequent (gamma, delta) =
  (List.map unlift_formula gamma, List.map unlift_formula delta)

(*
    Variable Context: used to track available variables during the reduction tree construction process.
*)
module VarCtx = struct
  let empty = ([], FormulaMap.empty)

  let split_prefix_matrix = function
    | LK.Exists (x, f) -> (x, f)
    | LK.ForAll (x, f) -> (x, f)
    | _ ->
        failwith
          "cannot split prefix and matrix if the outtermost logical symbol is \
           not a quantifier"

  let new_var available =
    let rec aux k =
      let a =
        let base = if k mod 2 = 0 then "a" else "b" in
        LK.Free (base ^ String.init (k / 2) (fun _ -> '\''))
      in
      if List.mem a available then aux (k + 1) else a
    in
    aux 0

  let first_available_for f (available, usage) =
    match
      List.find_opt
        (fun a ->
          (not (FormulaMap.mem f usage))
          || not (LK.VarSet.mem a (FormulaMap.find f usage)))
        available
    with
    | Some a ->
        ( ( available,
            FormulaMap.update f
              (function
                | Some sa -> Some (LK.VarSet.add a sa)
                | None -> Some (LK.VarSet.singleton a))
              usage ),
          a )
    | None ->
        let a = new_var available in
        ( ( a :: available,
            FormulaMap.update f
              (function
                | Some sa -> Some (LK.VarSet.add a sa)
                | None -> Some (LK.VarSet.singleton a))
              usage ),
          a )

  let first_nonavailable_for f (available, usage) =
    let a = new_var available in
    ( ( a :: available,
        FormulaMap.update f
          (function
            | Some sa -> Some (LK.VarSet.add a sa)
            | None -> Some (LK.VarSet.singleton a))
          usage ),
      a )
end

let reduction_tree s =
  let neg_reduction c =
    let c' =
      List.map
        (function NonReduced (Neg a) -> Reduced (Neg a) | other -> other)
        c
    in
    let a =
      List.filter_map
        (function NonReduced (Neg a) -> Some (NonReduced a) | _ -> None)
        c
    in
    (c', a)
  in
  let rec gen_pair_permutations acc s = function
    | (a, b) :: ab ->
        let acc = gen_pair_permutations acc (a :: s) ab in
        let acc = gen_pair_permutations acc (b :: s) ab in
        acc
    | [] -> List.rev s :: acc
  in
  let is_leaf (pi, lambda) =
    let pi', lambda' = unlift_sequent (pi, lambda) in
    List.exists (fun a -> List.exists (fun b -> a = b) lambda') pi'
  in
  (* k ≡ 0 *)
  let neg_left_condition (pi, _) =
    List.exists (function NonReduced (Neg _) -> true | _ -> false) pi
  in
  let neg_left_reduction vctx (pi, lambda) =
    let pi', a = neg_reduction pi in
    assert (not (a = []));
    (vctx, [ (pi', lambda @ a) ])
  in
  (* k ≡ 1 *)
  let neg_right_condition (_, lambda) =
    List.exists (function NonReduced (Neg _) -> true | _ -> false) lambda
  in
  let neg_right_reduction vctx (pi, lambda) =
    let lambda', a = neg_reduction lambda in
    assert (not (a = []));
    (vctx, [ (a @ pi, lambda') ])
  in
  (* k ≡ 2 *)
  let conj_left_condition (pi, _) =
    List.exists (function NonReduced (Conj _) -> true | _ -> false) pi
  in
  let conj_left_reduction vctx (pi, lambda) =
    let ab =
      List.concat
        (List.filter_map
           (function
             | NonReduced (Conj (a, b)) -> Some [ NonReduced a; NonReduced b ]
             | _ -> None)
           pi)
    in
    assert (not (ab = []));
    let pi' =
      List.map
        (function
          | NonReduced (Conj (a, b)) -> Reduced (Conj (a, b)) | other -> other)
        pi
    in
    (vctx, [ (ab @ pi', lambda) ])
  in
  (* k ≡ 3 *)
  let conj_right_condition (_, lambda) =
    List.exists (function NonReduced (Conj _) -> true | _ -> false) lambda
  in
  let conj_right_reduction vctx (pi, lambda) =
    let ab =
      List.filter_map
        (function
          | NonReduced (Conj (a, b)) -> Some (NonReduced a, NonReduced b)
          | _ -> None)
        lambda
    in
    assert (not (ab = []));
    let lambda' =
      List.map
        (function
          | NonReduced (Conj (a, b)) -> Reduced (Conj (a, b)) | other -> other)
        lambda
    in
    ( vctx,
      List.map
        (fun c -> (pi, lambda' @ c))
        (List.rev (gen_pair_permutations [] [] ab)) )
  in
  (* k ≡ 4 *)
  let disj_left_condition (pi, _) =
    List.exists (function NonReduced (Disj _) -> true | _ -> false) pi
  in
  let disj_left_reduction vctx (pi, lambda) =
    let ab =
      List.filter_map
        (function
          | NonReduced (Disj (a, b)) -> Some (NonReduced a, NonReduced b)
          | _ -> None)
        pi
    in
    assert (not (ab = []));
    let pi' =
      List.map
        (function
          | NonReduced (Disj (a, b)) -> Reduced (Disj (a, b)) | other -> other)
        pi
    in
    ( vctx,
      List.map
        (fun c -> (c @ pi', lambda))
        (List.rev (gen_pair_permutations [] [] ab)) )
  in
  (* k ≡ 5 *)
  let disj_right_condition (_, lambda) =
    List.exists (function NonReduced (Disj _) -> true | _ -> false) lambda
  in
  let disj_right_reduction vctx (pi, lambda) =
    let ab =
      List.concat
        (List.filter_map
           (function
             | NonReduced (Disj (a, b)) -> Some [ NonReduced a; NonReduced b ]
             | _ -> None)
           lambda)
    in
    assert (not (ab = []));
    let lambda' =
      List.map
        (function
          | NonReduced (Disj (a, b)) -> Reduced (Disj (a, b)) | other -> other)
        lambda
    in
    (vctx, [ (pi, lambda' @ ab) ])
  in
  (* k ≡ 6 *)
  let impl_left_condition (pi, _) =
    List.exists (function NonReduced (Impl _) -> true | _ -> false) pi
  in
  let impl_left_reduction vctx (pi, lambda) =
    let ab =
      List.filter_map
        (function
          | NonReduced (Impl (a, b)) -> Some (NonReduced a, NonReduced b)
          | _ -> None)
        pi
    in
    assert (not (ab = []));
    let pi =
      List.map
        (function
          | NonReduced (Impl (a, b)) -> Reduced (Impl (a, b)) | other -> other)
        pi
    in
    let rec gen_prefix_suffix acc (pi', lambda') = function
      | (a, b) :: ab ->
          let acc = gen_prefix_suffix acc (b :: pi', lambda') ab in
          let acc = gen_prefix_suffix acc (pi', a :: lambda') ab in
          acc
      | [] -> (pi', lambda') :: acc
    in
    ( vctx,
      List.map
        (fun (b, a) -> (List.rev b @ pi, lambda @ List.rev a))
        (gen_prefix_suffix [] ([], []) ab) )
  in
  (*
  (*
     This is the rule as it appears in the video: https://www.youtube.com/watch?v=QXw1aBn4VKg.
     It seems to be incorrect.
  *)
  let impl_left_reduction vctx (pi, lambda) =
    let ab =
      List.filter_map
        (function
          | NonReduced (Impl (a, b)) -> Some (NonReduced a, NonReduced b)
          | _ -> None)
        pi
    in
    assert (not (ab = []));
    let pi =
      List.map
        (function
          | NonReduced (Impl (a, b)) -> Reduced (Impl (a, b)) | other -> other)
        pi
    in
    let a, b = List.split ab in
    let sa = List.map (fun ai -> (pi, lambda @ [ ai ])) a in
    let sb = List.map (fun bi -> (bi :: pi, lambda)) b in
    (vctx, sa @ sb)
  in
  *)
  (* k ≡ 7 *)
  let impl_right_condition (_, lambda) =
    List.exists (function NonReduced (Impl _) -> true | _ -> false) lambda
  in
  let impl_right_reduction vctx (pi, lambda) =
    let a, b =
      List.split
        (List.filter_map
           (function
             | NonReduced (Impl (a, b)) -> Some (NonReduced a, NonReduced b)
             | _ -> None)
           lambda)
    in
    assert (not (a = []));
    assert (not (b = []));
    let lambda' =
      List.map
        (function
          | NonReduced (Impl (a, b)) -> Reduced (Impl (a, b)) | other -> other)
        lambda
    in
    (vctx, [ (a @ pi, lambda' @ b) ])
  in
  (* k ≡ 8 *)
  let forall_left_condition (pi, _) =
    List.exists
      (function
        | NonReduced (ForAll _) -> true
        | Reduced (ForAll _) -> true
        | _ -> false)
      pi
  in
  let forall_left_reduction vctx (pi, lambda) =
    let f =
      List.filter_map
        (function
          | NonReduced (ForAll (x, f)) -> Some (NonReduced (ForAll (x, f)))
          | Reduced (ForAll (x, f)) -> Some (Reduced (ForAll (x, f)))
          | _ -> None)
        pi
    in
    let vctx, f =
      List.fold_left
        (fun (vctx, f) fi ->
          let fi' = unlift_formula fi in
          let xi, gi = VarCtx.split_prefix_matrix fi' in
          let vctx, ai = VarCtx.first_available_for fi' vctx in
          (vctx, NonReduced (LK.substitute_term gi (LK.Var xi) (LK.Var ai)) :: f))
        (vctx, []) f
    in
    (vctx, [ (List.rev f @ pi, lambda) ])
  in
  (* k ≡ 9 *)
  let forall_right_condition (_, lambda) =
    List.exists (function NonReduced (ForAll _) -> true | _ -> false) lambda
  in
  let forall_right_reduction vctx (pi, lambda) =
    let f =
      List.filter_map
        (function
          | NonReduced (ForAll (x, f)) -> Some (Reduced (ForAll (x, f)))
          | _ -> None)
        lambda
    in
    let lambda' =
      List.map
        (function
          | NonReduced (ForAll (a, b)) -> Reduced (ForAll (a, b))
          | other -> other)
        lambda
    in
    let vctx, f =
      List.fold_left
        (fun (vctx, f) fi ->
          let fi' = unlift_formula fi in
          let xi, gi = VarCtx.split_prefix_matrix fi' in
          let vctx, ai = VarCtx.first_nonavailable_for fi' vctx in
          (vctx, NonReduced (LK.substitute_term gi (LK.Var xi) (LK.Var ai)) :: f))
        (vctx, []) f
    in
    (vctx, [ (pi, lambda' @ List.rev f) ])
  in
  (* k ≡ 10 *)
  let exists_left_condition (pi, _) =
    List.exists (function NonReduced (Exists _) -> true | _ -> false) pi
  in
  let exists_left_reduction vctx (pi, lambda) =
    let f =
      List.filter_map
        (function
          | NonReduced (Exists (x, f)) -> Some (Reduced (Exists (x, f)))
          | _ -> None)
        pi
    in
    let pi' =
      List.map
        (function
          | NonReduced (Exists (a, b)) -> Reduced (Exists (a, b))
          | other -> other)
        pi
    in
    let vctx, f =
      List.fold_left
        (fun (vctx, f) fi ->
          let fi' = unlift_formula fi in
          let xi, gi = VarCtx.split_prefix_matrix fi' in
          let vctx, ai = VarCtx.first_nonavailable_for fi' vctx in
          (vctx, NonReduced (LK.substitute_term gi (LK.Var xi) (LK.Var ai)) :: f))
        (vctx, []) f
    in
    (vctx, [ (List.rev f @ pi', lambda) ])
  in
  (* k ≡ 11 *)
  let exists_right_condition (_, lambda) =
    List.exists
      (function
        | NonReduced (Exists _) -> true
        | Reduced (Exists _) -> true
        | _ -> false)
      lambda
  in
  let exists_right_reduction vctx (pi, lambda) =
    let f =
      List.filter_map
        (function
          | NonReduced (Exists (x, f)) -> Some (NonReduced (Exists (x, f)))
          | Reduced (Exists (x, f)) -> Some (Reduced (Exists (x, f)))
          | _ -> None)
        lambda
    in
    let vctx, f =
      List.fold_left
        (fun (vctx, f) fi ->
          let fi' = unlift_formula fi in
          let xi, gi = VarCtx.split_prefix_matrix fi' in
          let vctx, ai = VarCtx.first_available_for fi' vctx in
          (vctx, NonReduced (LK.substitute_term gi (LK.Var xi) (LK.Var ai)) :: f))
        (vctx, []) f
    in
    (vctx, [ (pi, lambda @ List.rev f) ])
  in
  let reductions =
    [
      ("¬:left", neg_left_condition, neg_left_reduction);
      ("¬:right", neg_right_condition, neg_right_reduction);
      ("∧:left", conj_left_condition, conj_left_reduction);
      ("∧:right", conj_right_condition, conj_right_reduction);
      ("∨:left", disj_left_condition, disj_left_reduction);
      ("∨:right", disj_right_condition, disj_right_reduction);
      ("⊃:left", impl_left_condition, impl_left_reduction);
      ("⊃:right", impl_right_condition, impl_right_reduction);
      ("∀:left", forall_left_condition, forall_left_reduction);
      ("∀:right", forall_right_condition, forall_right_reduction);
      ("∃:left", exists_left_condition, exists_left_reduction);
      ("∃:right", exists_right_condition, exists_right_reduction);
    ]
  in
  let rec aux s0 g vctx =
    let g, vctx, s1 =
      List.fold_left
        (*
         * g = current tree
         * vctx = variables available at this point
         * s1 = sequents obtained so far for next stage
         *)
          (fun (g, vctx, s1) (k, (pi, lambda)) ->
          let vctx, indexed_next_sequents =
            if is_leaf (pi, lambda) then (vctx, [])
            else
              let m = List.length reductions in
              let indexed_reductions =
                List.sort Stdlib.compare
                  (List.mapi (fun i r -> ((i - k + m) mod m, r)) reductions)
              in
              match
                List.find_opt
                  (fun (_, (_, condition, _)) -> condition (pi, lambda))
                  indexed_reductions
              with
              | Some (i, ((* reduction_name *) _, _, reduction)) ->
                  let vctx, ss = reduction vctx (pi, lambda) in
                  (*
                  Printf.printf "DEBUG: %s: %s ~~> [%s]\n%!" reduction_name
                    (LK.string_of_sequent (unlift_sequent (pi, lambda)))
                    (String.concat "; "
                       (List.map
                          (fun s -> LK.string_of_sequent (unlift_sequent s))
                          ss));
                          *)
                  (vctx, List.map (fun s -> (k + i + 1, s)) ss)
              | None ->
                  (* k ≡ 12 *)
                  (vctx, [ (k, (pi, lambda)) ])
          in
          let _, next_sequents = List.split indexed_next_sequents in
          let new_node = { nod_stage = k; nod_children = next_sequents } in
          ( SequentMap.add (pi, lambda) new_node g,
            vctx,
            s1 @ indexed_next_sequents ))
        (g, vctx, []) s0
    in
    match s1 with [] -> (g, s0) | _ -> aux s1 g vctx
  in
  let g, _ = aux [ (0, lift_sequent s) ] SequentMap.empty VarCtx.empty in
  g

let tex_of_node_formula = function
  | NonReduced a -> LK.tex_of_formula a
  | Reduced a -> Printf.sprintf "{\\color{red}%s}" (LK.tex_of_formula a)

let tex_of_node_sequent (gamma, delta) =
  Printf.sprintf "%s \\rightarrow %s"
    (String.concat ", " (List.map tex_of_node_formula gamma))
    (String.concat ", " (List.map tex_of_node_formula delta))

let tex_of_tree rt =
  let root, _ =
    List.find
      (fun (_, { nod_stage; _ }) -> nod_stage = 0)
      (SequentMap.bindings rt)
  in
  let rec aux k u =
    let { nod_stage; nod_children } = SequentMap.find u rt in
    if nod_stage < k then "node {$\\dots$} "
    else
      let children =
        List.map
          (fun v -> Printf.sprintf "child {%s}" (aux (k + 1) v))
          nod_children
      in
      Printf.sprintf "node {$%s$} %s" (tex_of_node_sequent u)
        (String.concat " " children)
  in
  Printf.sprintf
    "\\begin{tikzpicture}\n\
     [grow via three points={one child at (0,1) and two children at (-5,1) and \
     (5,1)}]\n\
     \\%s;\n\
     \\end{tikzpicture}"
    (aux 0 root)
