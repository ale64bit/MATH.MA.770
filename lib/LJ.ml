let ( let* ) = Result.bind

let validate_sequent (ant, suc) =
  let* vs = LK.validate_sequent (ant, suc) in
  match suc with
  | [] -> Ok vs
  | [ _ ] -> Ok vs
  | _ ->
      Error
        "succedent cannot have more than one formula in intuitionistic proofs"
