(** Support for assigns and dos **)

open Common.Error
open Common
open Printf

type environment = Smtlib.sort symtab

let reduce_sort (inp : L1.sort) : Smtlib.sort = inp

let reduce_datatype (inp : L1.data_def) : Smtlib.data_def = inp

let rec reduce_expr (dts : L1.data_def list) (inp : L1.expr) : Smtlib.expr =
  let red = reduce_expr dts in
  match inp with
  | True -> True
  | False -> False
  | Num v -> Num v
  | Str v -> Str v
  | Let (var, exp, body) -> Let (var, red exp, red body)
  | If (test_exp, then_exp, else_exp) ->
      If (red test_exp, red then_exp, red else_exp)
  | Call (f, args) -> Call (f, List.map red args)
  | Project (f, arg) -> Project (f, red arg)
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Select (f, arg) -> Select (red f, red arg)
  | Not arg -> Not (red arg)
  | And (arg1, arg2) -> And (red arg1, red arg2)
  | Or (arg1, arg2) -> Or (red arg1, red arg2)
  | Implies (arg1, arg2) -> Implies (red arg1, red arg2)
  | Plus (arg1, arg2) -> Plus (red arg1, red arg2)
  | Minus (arg1, arg2) -> Minus (red arg1, red arg2)
  | Times (arg1, arg2) -> Times (red arg1, red arg2)
  | Concat (arg1, arg2) -> Concat (red arg1, red arg2)
  | Eq (arg1, arg2) -> Eq (red arg1, red arg2)
  | Is (arg1, arg2) -> Is (red arg1, arg2)
  | Prefix (arg1, arg2) -> Prefix (red arg1, red arg2)
  | Suffix (arg1, arg2) -> Suffix (red arg1, red arg2)
  | Contains (arg1, arg2) -> Contains (red arg1, red arg2)
  | Lt (arg1, arg2) -> Lt (red arg1, red arg2)
  | Lte (arg1, arg2) -> Lte (red arg1, red arg2)
  | Gt (arg1, arg2) -> Gt (red arg1, red arg2)
  | Gte (arg1, arg2) -> Gte (red arg1, red arg2)
  | Length e -> Length (red e)
  | Unit e -> Unit (red e)
  | Const (e, t) -> Const (red e, reduce_sort t)
  | As (e, t) -> As (red e, reduce_sort t)
  | Forall (ps, b) ->
      Forall (List.map (fun (x, y) -> (x, reduce_sort y)) ps, red b)
  | Exists (ps, b) ->
      Exists (List.map (fun (x, y) -> (x, reduce_sort y)) ps, red b)
  | Do [a] -> red a
  | Do (Assign (Call (lhs, []), rhs) :: after) ->
      let new_after = red (Do after) in
      Let (lhs, red rhs, new_after)
  | Do (If (test, left, right) :: after) as e -> (
      let new_left = red left in
      let new_right = red right in
      let new_after = red (Do after) in
      match (new_left, new_right) with
      | Let (s1, _, _), Let (s2, _, _) when s1.value = s2.value ->
          let call = Smtlib.If (red test, new_left, new_right) in
          Let (s1, call, new_after)
      | _, _ ->
          raise (ReduceUpdateError (sprintf "Do-If: %s" (L1.show_expr e))) )
  | Do _ as e -> raise (ReduceUpdateError (sprintf "Do: %s" (L1.show_expr e)))
  | Assign (Call (lhs, []), rhs) -> Let (lhs, red rhs, Call (lhs, []))
  | Assign _ as e ->
      raise (ReduceUpdateError (sprintf "Assign: %s" (L1.show_expr e)))

let reduce_command (dts : L1.data_def list) : L1.command -> Smtlib.command =
  function
  | Check -> Check
  | Push -> Push
  | Pop -> Pop
  | Print (Left e) -> Print (Left (reduce_expr dts e))
  | Print (Right e) -> Print (Right e)
  | Assume e -> Assume (reduce_expr dts e)
  | Assert e -> Assert (reduce_expr dts e)
  | Choose ((x, sx), Some (y, sy), a, b) ->
      Choose
        ( (x, reduce_sort sx)
        , Some (y, reduce_sort sy)
        , Option.map (reduce_expr dts) a
        , Option.map (reduce_expr dts) b )
  | Choose ((x, sx), None, a, b) ->
      Choose
        ( (x, reduce_sort sx)
        , None
        , Option.map (reduce_expr dts) a
        , Option.map (reduce_expr dts) b )

let reduce_fun (dts : L1.data_def list) (defn0 : L1.fun_def) : Smtlib.fun_def
    =
  let new_params =
    List.map (fun (n, s) -> (n, reduce_sort s)) defn0.params
  in
  let new_sort = reduce_sort defn0.sort in
  let new_body = Option.map (reduce_expr dts) defn0.body in
  { name= defn0.name
  ; recursive= defn0.recursive
  ; params= new_params
  ; body= new_body
  ; sort= new_sort }

let reduce (prog : L1.program) : Smtlib.program =
  let new_datatypes = List.map reduce_datatype prog.datatypes in
  let new_funs = List.map (reduce_fun prog.datatypes) prog.funs in
  let new_body = List.map (reduce_command prog.datatypes) prog.body in
  {funs= new_funs; datatypes= new_datatypes; body= new_body}
