type var = string
type app = string * var list

type t =
  | Succ of string * var list * var
  | Const of string * var list * Nat.t
  | Id of string * var list * var
  | Subs of string * var list * string * app list
  | Ind0 of {
      ind0_base_f : string;
      ind0_base_zero : Nat.t;
      ind0_base_q : Nat.t;
      ind0_step_f : string;
      ind0_step_y' : string;
      ind0_step_xi : string;
      ind0_step_y : string;
      ind0_step_app : app;
    }
  | Ind1 of {
      ind1_base_f : string;
      ind1_base_zero : Nat.t;
      ind1_base_xs : var list;
      ind1_base_psi : app;
      ind1_step_f : string;
      ind1_step_y' : string;
      ind1_step_xs : var list;
      ind1_step_xi : string;
      ind1_step_y : string;
      ind1_step_app : app;
      ind1_step_args : var list;
    }

let all_distinct xs =
  List.length (List.sort_uniq Stdlib.compare xs) = List.length xs

let is_valid = function
  | Succ (_, [ x ], x') -> x = x'
  | Const (_, xs, _) -> all_distinct xs
  | Id (_, xs, x) -> all_distinct xs && List.mem x xs
  | Subs (_, xs, _, apps) ->
      all_distinct xs && List.for_all (fun (_, ys) -> xs = ys) apps
  | Ind0
      {
        ind0_base_f;
        ind0_base_zero;
        ind0_step_f;
        ind0_step_y';
        ind0_step_y;
        ind0_step_app = f', ys;
        _;
      } ->
      ind0_base_f = ind0_step_f && ind0_base_zero = Zero
      && ind0_step_y' = ind0_step_y && ind0_base_f = f'
      && ys = [ ind0_step_y ]
  | Ind1
      {
        ind1_base_f;
        ind1_base_zero;
        ind1_base_xs;
        ind1_base_psi = _, psi_xs;
        ind1_step_f;
        ind1_step_y';
        ind1_step_xs;
        ind1_step_y;
        ind1_step_app = _, app_xs;
        ind1_step_args;
        _;
      } ->
      ind1_base_f = ind1_step_f && ind1_base_zero = Zero
      && ind1_base_xs = psi_xs
      && ind1_base_xs = ind1_step_xs
      && ind1_base_xs = ind1_step_args
      && ind1_step_y' = ind1_step_y
      && app_xs = ind1_step_y :: ind1_base_xs
  | _ -> false

let same_arity xs ys = List.length xs = List.length ys

let rec eval env f xs =
  let ( let* ) = Result.bind in
  match
    List.find_opt
      (function
        | Succ (f', _, _) -> f = f'
        | Const (f', _, _) -> f = f'
        | Id (f', _, _) -> f = f'
        | Subs (f', _, _, _) -> f = f'
        | Ind0 { ind0_base_f; _ } -> f = ind0_base_f
        | Ind1 { ind1_base_f; _ } -> f = ind1_base_f)
      env
  with
  | Some (Succ _) -> (
      match xs with
      | [ x ] -> Ok (Nat.Succ x)
      | _ -> Error (Printf.sprintf "type I: %s: invalid number of arguments" f))
  | Some (Const (_, ys, q)) ->
      if same_arity xs ys then Ok q
      else Error (Printf.sprintf "type II: %s: invalid number of arguments" f)
  | Some (Id (_, ys, y)) ->
      if same_arity xs ys then
        let i, _ =
          List.find (fun (_, x) -> x = y) (List.mapi (fun i x -> (i, x)) ys)
        in
        Ok (List.nth xs i)
      else Error (Printf.sprintf "type III: %s: invalid number of arguments" f)
  | Some (Subs (_, _, g, hs)) ->
      let args = List.map (fun (h, _) -> eval env h xs) hs in
      let* args =
        List.fold_left
          (fun acc_res arg_res ->
            let* acc = acc_res in
            let* arg = arg_res in
            Ok (arg :: acc))
          (Ok []) args
      in
      eval env g (List.rev args)
  | Some (Ind0 { ind0_base_q; ind0_step_xi; _ }) -> (
      match xs with
      | [ Zero ] -> Ok ind0_base_q
      | [ Succ y ] ->
          let* tmp = eval env f [ y ] in
          eval env ind0_step_xi [ y; tmp ]
      | _ -> Error (Printf.sprintf "type Va: %s: invalid number of arguments" f)
      )
  | Some (Ind1 { ind1_base_xs; ind1_base_psi = psi, _; ind1_step_xi; _ }) ->
      if 1 + List.length ind1_base_xs = List.length xs then
        match xs with
        | Zero :: xs' -> eval env psi xs'
        | Succ y :: xs' ->
            let* tmp = eval env f (y :: xs') in
            eval env ind1_step_xi ([ y; tmp ] @ xs')
        | _ ->
            Error
              (Printf.sprintf
                 "type Vb: %s: invalid number of arguments: want %d, got %d" f
                 (List.length ind1_base_xs + 1)
                 (List.length xs))
      else
        Error
          (Printf.sprintf
             "type Vb: %s: invalid number of arguments: want %d, got %d" f
             (List.length ind1_base_xs + 1)
             (List.length xs))
  | None -> Error (Printf.sprintf "no such function '%s'" f)
