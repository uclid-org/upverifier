open Printf
open Smtlib
open Common
open Common.Error
open Common.Suggestion
open Value
open Sort
open Util

let rec display_value = function
  | Num x -> sprintf "%d" x
  | Str x -> x
  | Bool b -> if b then "true" else "false"
  | Seq ls -> String.concat " . " (List.map display_value ls)
  | Array (ps, d, t) ->
      let rec print_array ps d t =
        match ps with
        | [] -> sprintf "const(%s, %s)" (display_value d) (display_sort t)
        | p :: ps ->
            sprintf "(%s\n\t[%s -> %s])" (print_array ps d t)
              (display_value (fst p))
              (display_value (snd p))
      in
      print_array ps d t
  | Data xs ->
      let cons = fst xs in
      let names = fst (List.split (snd xs)) in
      let values = List.map display_value (snd (List.split (snd xs))) in
      if List.length names > 0 then
        sprintf "%s(%s)" cons
          (String.concat ", "
             (List.map2
                (fun _ v -> sprintf "%s" v)
                (List.map (fun x -> x) names)
                values ) )
      else cons

let interp_unary_primitive e arg =
  match (e, arg) with
  | Not _, Bool false -> Some (Bool true)
  | Not _, Bool true -> Some (Bool false)
  | Not _, _ -> None
  | _ -> None

let rec prefix needle haystack =
  match (needle, haystack) with
  | x :: xs, y :: ys -> x = y && prefix xs ys
  | [], _ -> true
  | _, [] -> false

let rec drop sequence count =
  match (count, sequence) with
  | x, y when x <= 0 -> y
  | x, _ :: ys -> drop ys (x - 1)
  | _, [] -> []

let suffix needle haystack =
  let diff = List.length haystack - List.length needle in
  let tail = drop haystack diff in
  needle = tail

let rec contains needle haystack =
  match haystack with
  | _ :: xs -> prefix needle haystack || contains needle xs
  | [] -> false

let interp_binary_primitive e arg1 arg2 =
  match (e, arg1, arg2) with
  | And (_, _), Bool x1, Bool x2 -> Some (Bool (x1 && x2))
  | Or (_, _), Bool x1, Bool x2 -> Some (Bool (x1 || x2))
  | Plus (_, _), Num x1, Num x2 -> Some (Num (x1 + x2))
  | Minus (_, _), Num x1, Num x2 -> Some (Num (x1 - x2))
  | Times (_, _), Num x1, Num x2 -> Some (Num (x1 * x2))
  | Concat (_, _), Seq x1, Seq x2 -> Some (Seq (x1 @ x2))
  | Eq (_, _), a, b -> Some (Bool (a = b))
  | Prefix (_, _), Seq needle, Seq haystack ->
      Some (Bool (prefix needle haystack))
  | Suffix (_, _), Seq needle, Seq haystack ->
      Some (Bool (suffix needle haystack))
  | Contains (_, _), Seq needle, Seq haystack ->
      Some (Bool (contains needle haystack))
  | Lt (_, _), Num x1, Num x2 -> Some (Bool (x1 < x2))
  | Lte (_, _), Num x1, Num x2 -> Some (Bool (x1 <= x2))
  | Gt (_, _), Num x1, Num x2 -> Some (Bool (x1 > x2))
  | Gte (_, _), Num x1, Num x2 -> Some (Bool (x1 >= x2))
  | _ -> None

let rec interp_term (funs : fun_def list) (datatypes : data_def list)
    (env : environment) : expr -> value = function
  | Num x -> Num x
  | Str x -> Str x
  | Call (var, []) when Symtab.mem var.value env -> Symtab.find var.value env
  | Let (var, exp, body) ->
      let env =
        env |> Symtab.add var.value (interp_term funs datatypes env exp)
      in
      interp_term funs datatypes env body
  | If (test_exp, then_exp, else_exp) ->
      if interp_term funs datatypes env test_exp <> Bool false then
        interp_term funs datatypes env then_exp
      else interp_term funs datatypes env else_exp
  | Call (f, args) when is_fun funs f ->
      let defn = get_fun funs f in
      if List.length args = List.length defn.params then
        let pairs =
          args
          |> List.map (interp_term funs datatypes env)
          |> List.combine
               (fst
                  (List.split
                     (List.map (fun (p, s) -> (p.value, s)) defn.params) ) )
        in
        let fenv =
          List.fold_left (fun acc (x, y) -> Symtab.add x y acc) env pairs
        in
        match defn.body with
        | Some body -> interp_term funs datatypes fenv body
        | None ->
            raise
              (Stuck
                 (sprintf "Trying to interp an uninterpreted function %s"
                    (show_pstring f) ) )
      else
        raise
          (Stuck
             (sprintf
                "Number of arguments (%d) does not match number of parameters (%d) at function call %s"
                (List.length args) (List.length defn.params) (show_pstring f) )
          )
  | Call (f, args) when is_cons datatypes f ->
      let case = get_cons_case datatypes f in
      let cons = fst case in
      let sels = snd case in
      let names = List.map (fun x -> x.value) (fst (List.split sels)) in
      if List.length args = List.length sels then
        let vals = List.map (interp_term funs datatypes env) args in
        Data (cons.value, List.combine names vals)
      else
        raise
          (Stuck
             (sprintf
                "Number of arguments (%d) does not match number of parameters (%d) at constructor call %s"
                (List.length args) (List.length sels) (show_pstring f) ) )
  | Call (f, args) -> (
      let length = List.length args in
      let candidates =
        ( if length = 0 then
          List.of_seq (Seq.map (fun x -> fst x) (to_list env))
        else [] )
        @ List.filter_map
            (fun (x : fun_def) ->
              if List.length x.params = length then Some x.name.value
              else None )
            funs
        @ List.flatten
            (List.map
               (fun x ->
                 List.filter_map
                   (fun y ->
                     if List.length (snd y) = length then Some (fst y).value
                     else None )
                   x.cases )
               datatypes )
      in
      match suggest candidates f.value with
      | Some best ->
          raise
            (Stuck
               (sprintf "Unknown function %s\nDid you mean \"%s\"?"
                  (show_pstring f) best ) )
      | None ->
          raise
            (Stuck
               (sprintf "Unknown function %s\nNo candidates to suggest."
                  (show_pstring f) ) ) )
  | Project (f, arg) as e when is_sel datatypes f -> (
      let v = interp_term funs datatypes env arg in
      match v with
      | Data (c, ls) -> (
          let found_opt = List.find_opt (fun x -> fst x = f.value) ls in
          match found_opt with
          | Some l -> snd l
          | None ->
              raise
                (Stuck
                   (sprintf
                      "Cannot project \"%s\" on %sSelector \"%s\" doesn't exist for constructor \"%s\""
                      (show_expr arg) (show_pstring f) f.value c ) ) )
      | _ ->
          raise (Stuck (Printf.sprintf "Failed project: %s\n" (show_expr e)))
      )
  | Project _ as e ->
      raise (Stuck (Printf.sprintf "Failed project: %s\n" (show_expr e)))
  | Select (from, index) as e -> (
      let new_from = interp_term funs datatypes env from in
      let new_index = interp_term funs datatypes env index in
      match new_from with
      | Array (ps, d, _) -> (
        match List.find_opt (fun (x, _) -> x = new_index) ps with
        | Some (_, y) -> y
        | None -> d )
      | _ ->
          raise (Stuck (Printf.sprintf "Failed select: %s\n" (show_expr e)))
      )
  | Not arg as e -> (
    match interp_unary_primitive e (interp_term funs datatypes env arg) with
    | Some v -> v
    | None -> raise (Stuck (Printf.sprintf "Failed not: %s\n" (show_expr e)))
    )
  | And (arg1, arg2) as e -> (
    match interp_term funs datatypes env arg1 with
    | Bool true -> interp_term funs datatypes env arg2
    | Bool false -> Bool false
    | _ -> raise (Stuck (Printf.sprintf "Failed and: %s\n" (show_expr e))) )
  | Or (arg1, arg2) as e -> (
    match interp_term funs datatypes env arg1 with
    | Bool false -> interp_term funs datatypes env arg2
    | Bool true -> Bool true
    | _ -> raise (Stuck (Printf.sprintf "Failed or: %s\n" (show_expr e))) )
  | Implies (arg1, arg2) as e -> (
    match interp_term funs datatypes env arg1 with
    | Bool true -> interp_term funs datatypes env arg2
    | Bool false -> Bool true
    | _ -> raise (Stuck (Printf.sprintf "Failed implies: %s\n" (show_expr e)))
    )
  | ( Plus (arg1, arg2)
    | Minus (arg1, arg2)
    | Times (arg1, arg2)
    | Concat (arg1, arg2)
    | Eq (arg1, arg2)
    | Prefix (arg1, arg2)
    | Suffix (arg1, arg2)
    | Contains (arg1, arg2)
    | Lt (arg1, arg2)
    | Lte (arg1, arg2)
    | Gt (arg1, arg2)
    | Gte (arg1, arg2) ) as e -> (
    match
      let v1 = interp_term funs datatypes env arg1 in
      let v2 = interp_term funs datatypes env arg2 in
      interp_binary_primitive e v1 v2
    with
    | Some v -> v
    | None ->
        raise
          (Stuck
             (Printf.sprintf "Failed binary primitive: %s\n" (show_expr e))
          ) )
  | True -> Bool true
  | False -> Bool false
  | As (e, _) -> interp_term funs datatypes env e
  | Length e -> (
    match interp_term funs datatypes env e with
    | Seq xs -> Num (List.length xs)
    | _ ->
        raise
          (Stuck
             (Printf.sprintf "Can't get length of non sequence: %s\n"
                (show_expr e) ) ) )
  | Unit e ->
      let v = interp_term funs datatypes env e in
      Seq [v]
  | Const (e, t) ->
      let v = interp_term funs datatypes env e in
      Array ([], v, t)
  | Update (from, index, plug) as e -> (
      let new_from = interp_term funs datatypes env from in
      let new_index = interp_term funs datatypes env index in
      let new_plug = interp_term funs datatypes env plug in
      match new_from with
      | Array (ps, d, t) ->
          let new_pairs =
            if List.mem_assoc new_index ps then
              (new_index, new_plug) :: List.remove_assoc new_index ps
            else (new_index, new_plug) :: ps
          in
          Array (new_pairs, d, t)
      | _ ->
          raise (Stuck (Printf.sprintf "Failed update: %s\n" (show_expr e)))
      )
  | Is (arg1, c1) as e -> (
      let t1 = interp_term funs datatypes env arg1 in
      match t1 with
      | Data (c2, _) -> Bool (c1.value = c2)
      | _ -> raise (Stuck (Printf.sprintf "Failed is: %s\n" (show_expr e))) )
  | Forall (params, body) as e ->
      List.iter
        (fun (n, s) ->
          match s with
          | SortCall (f, _) when is_enum datatypes f -> ()
          | _ ->
              raise
                (Stuck
                   (sprintf "Expected an Enum type but got \"%s\" %s"
                      (show_sort s) (show_pstring n) ) ) )
        params ;
      let param_names = fst (List.split params) in
      let param_instances =
        List.map
          (get_instances_of_sort 0 datatypes)
          (snd (List.split params))
      in
      let param_instances = cartesian param_instances in
      List.fold_left
        (fun acc instance ->
          let bindings = List.combine param_names instance in
          let x =
            List.fold_left (fun acc (n, e) -> Let (n, e, acc)) body bindings
          in
          let v = interp_term funs datatypes env x in
          match (acc, v) with
          | Bool a, Bool b -> Bool (a && b)
          | _ ->
              raise
                (Stuck (Printf.sprintf "Failed forall: %s\n" (show_expr e)))
          )
        (Bool true) param_instances
  | Exists (params, body) as e ->
      List.iter
        (fun (n, s) ->
          match s with
          | SortCall (f, _) when is_enum datatypes f -> ()
          | _ ->
              raise
                (Stuck
                   (sprintf "Expected an Enum type but got \"%s\" %s"
                      (show_sort s) (show_pstring n) ) ) )
        params ;
      let param_names = fst (List.split params) in
      let param_instances =
        List.map
          (get_instances_of_sort 0 datatypes)
          (snd (List.split params))
      in
      let param_instances = cartesian param_instances in
      List.fold_left
        (fun acc instances ->
          let bindings = List.combine param_names instances in
          let x =
            List.fold_left (fun acc (n, e) -> Let (n, e, acc)) body bindings
          in
          let v = interp_term funs datatypes env x in
          match (acc, v) with
          | Bool a, Bool b -> Bool (a || b)
          | _ ->
              raise
                (Stuck (Printf.sprintf "Failed exists: %s\n" (show_expr e)))
          )
        (Bool false) param_instances
