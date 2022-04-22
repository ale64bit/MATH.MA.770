(* Basic representation of natural numbers *)
type t = Zero | Succ of t

let rec int_of_nat = function Zero -> 0 | Succ x -> int_of_nat x + 1
let rec nat_of_int = function 0 -> Zero | x -> Succ (nat_of_int (x - 1))
