open List

let revhd l = hd (rev l)
let revtl l = rev (tl (rev l))

let exch start l =
  let rec aux i = function
    | c :: d :: xs when i = start -> d :: c :: xs
    | x :: xs -> x :: aux (i + 1) xs
    | [] -> []
  in
  aux 0 l
