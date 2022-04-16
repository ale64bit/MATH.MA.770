type node_formula = NonReduced of LK.formula | Reduced of LK.formula
type node_sequent = node_formula list * node_formula list
type node = { nod_stage : int; nod_children : node_sequent list }

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
  let neg_left_reduction (pi, lambda) =
    let pi', a = neg_reduction pi in
    assert (not (a = []));
    [ (pi', lambda @ a) ]
  in
  (* k ≡ 1 *)
  let neg_right_reduction (pi, lambda) =
    let lambda', a = neg_reduction lambda in
    assert (not (a = []));
    [ (a @ pi, lambda') ]
  in
  (* k ≡ 2 *)
  let conj_left_reduction (pi, lambda) =
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
    [ (ab @ pi', lambda) ]
  in
  (* k ≡ 3 *)
  let conj_right_reduction (pi, lambda) =
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
    List.map
      (fun c -> (pi, lambda' @ c))
      (List.rev (gen_pair_permutations [] [] ab))
  in
  (* k ≡ 4 *)
  let disj_left_reduction (pi, lambda) =
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
    List.map
      (fun c -> (c @ pi', lambda))
      (List.rev (gen_pair_permutations [] [] ab))
  in
  (* k ≡ 5 *)
  let disj_right_reduction (pi, lambda) =
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
    [ (pi, lambda' @ ab) ]
  in
  (* k ≡ 6 *)
  let impl_left_reduction (pi, lambda) =
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
    List.map
      (fun (b, a) -> (List.rev b @ pi, lambda @ List.rev a))
      (gen_prefix_suffix [] ([], []) ab)
  in
  (*
    (* 
      This is the rule as it appears in the video: https://www.youtube.com/watch?v=QXw1aBn4VKg.
      It seems to be incorrect.
    *)
  let impl_left_reduction (pi, lambda) =
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
    sa @ sb
  in
  *)
  (* k ≡ 7 *)
  let impl_right_reduction (pi, lambda) =
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
    [ (a @ pi, lambda' @ b) ]
  in
  (* k ≡ 8 *)
  (*
  let forall_left_reduction (pi, lambda) =
    let a =
      List.filter_map
        (function
          | NonReduced (ForAll (x, a)) -> Some (NonReduced (ForAll (x, a)))
          | _ -> None)
        pi
    in
    todo
  in
  *)
  (* k ≡ 9 *)
  (* TODO *)
  (* k ≡ 10 *)
  (* TODO *)
  (* k ≡ 11 *)
  (* TODO *)
  (* k ≡ 12 *)
  let rec aux k s0 g =
    let g, _, s1 =
      List.fold_left
        (*
         * g = current tree
         * xs = variables available at this point
         * s1 = sequents obtained so far for next stage
         *)
          (fun (g, xs, s1) (pi, lambda) ->
          let xs, next_sequents =
            if is_leaf (pi, lambda) then (xs, [])
            else if
              List.exists
                (function NonReduced (Neg _) -> true | _ -> false)
                pi
            then (xs, neg_left_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Neg _) -> true | _ -> false)
                lambda
            then (xs, neg_right_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Conj _) -> true | _ -> false)
                pi
            then (xs, conj_left_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Conj _) -> true | _ -> false)
                lambda
            then (xs, conj_right_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Disj _) -> true | _ -> false)
                pi
            then (xs, disj_left_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Disj _) -> true | _ -> false)
                lambda
            then (xs, disj_right_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Impl _) -> true | _ -> false)
                pi
            then (xs, impl_left_reduction (pi, lambda))
            else if
              List.exists
                (function NonReduced (Impl _) -> true | _ -> false)
                lambda
            then (xs, impl_right_reduction (pi, lambda))
              (*
            else if
              List.exists
                (function NonReduced (ForAll _) -> true | _ -> false)
                pi
            then (xs, forall_left_reduction (pi, lambda))
          *)
            else (xs, [ (pi, lambda) ])
          in
          let new_node = { nod_stage = k; nod_children = next_sequents } in
          (SequentMap.add (pi, lambda) new_node g, xs, s1 @ next_sequents))
        (g, LK.VarSet.empty, []) s0
    in
    match s1 with
    | [] -> (g, s0)
    | s0' when s0 = s0' -> (g, s0)
    | _ -> aux (k + 1) s1 g
  in
  let g, _ = aux 0 [ lift_sequent s ] SequentMap.empty in
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
