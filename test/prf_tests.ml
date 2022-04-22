open OUnit2
open Prf

let parse_prf_line (line : string) =
  let linebuf = Lexing.from_string line in
  let prf = Parser.prf_line Lexer.token linebuf in
  assert (PRF.is_valid prf);
  prf

let is_comment line = String.length line > 0 && String.sub line 0 1 = "%"

let load_prf channel =
  let rec aux acc =
    let optional_line, continue = Lexer.line channel in
    let acc =
      match optional_line with
      | Some line when (not (line = "\n")) && not (is_comment line) ->
          parse_prf_line line :: acc
      | _ -> acc
    in
    if continue then aux acc else acc
  in
  aux []

let env = load_prf (Lexing.from_channel (open_in "../../../data/prf.txt"))

let gen_binary_args n =
  List.flatten
    (List.init (n + 1) (fun a -> List.init (n + 1) (fun b -> (a, b))))

let test_binary_fn f cases =
  List.iter
    (fun (a, b, want) ->
      let res = PRF.eval env f [ Nat.nat_of_int a; Nat.nat_of_int b ] in
      match res with
      | Ok got ->
          let msg = Printf.sprintf "evaluating %s(%d,%d)" f a b in
          assert_equal ~printer:string_of_int ~msg (Nat.int_of_nat got) want
      | Error msg -> assert_failure (Printf.sprintf "%s(%d,%d): %s" f a b msg))
    cases

let test_binary_pred f cases =
  List.iter
    (fun (a, b, want) ->
      let res = PRF.eval env f [ Nat.nat_of_int a; Nat.nat_of_int b ] in
      match res with
      | Ok got ->
          let msg = Printf.sprintf "evaluating %s(%d,%d)" f a b in
          assert_equal ~printer:string_of_bool ~msg (got = Zero) want
      | Error msg -> assert_failure (Printf.sprintf "%s(%d,%d): %s" f a b msg))
    cases

(* Verify that the defined PRFs do represent the intended function/predicate *)

let add_tests _ =
  let n = 20 in
  let cases = List.map (fun (a, b) -> (a, b, a + b)) (gen_binary_args n) in
  test_binary_fn "ADD" cases

let mult_tests _ =
  let n = 20 in
  let cases = List.map (fun (a, b) -> (a, b, a * b)) (gen_binary_args n) in
  test_binary_fn "MULT" cases

let exp_tests _ =
  let rec exp a b = if b = 0 then 1 else a * exp a (b - 1) in
  let n = 6 in
  let cases = List.map (fun (a, b) -> (a, b, exp a b)) (gen_binary_args n) in
  test_binary_fn "EXP" cases

let sub_tests _ =
  let n = 20 in
  let max a b = if a > b then a else b in
  let cases =
    List.map (fun (a, b) -> (a, b, max 0 (a - b))) (gen_binary_args n)
  in
  test_binary_fn "SUB" cases

let eq_tests _ =
  let n = 20 in
  let cases = List.map (fun (a, b) -> (a, b, a = b)) (gen_binary_args n) in
  test_binary_pred "EQ" cases

let lt_tests _ =
  let n = 20 in
  let cases = List.map (fun (a, b) -> (a, b, a < b)) (gen_binary_args n) in
  test_binary_pred "LT" cases

let suite =
  "PRFTests"
  >::: [
         "ADD" >:: add_tests;
         "MULT" >:: mult_tests;
         "EXP" >:: exp_tests;
         "SUB" >:: sub_tests;
         "EQ" >:: eq_tests;
         "LT" >:: lt_tests;
       ]

let () = run_test_tt_main suite
