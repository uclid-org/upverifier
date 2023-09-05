(** Fix left-hand-sides of assigns **)

open Common.Error
open Common
open Printf

type environment = L1.sort symtab

let reduce_sort (inp : L1.sort) : L1.sort = inp

let reduce_datatype (inp : L1.data_def) : L1.data_def = inp

let reduce_record_update_helper dts sel from rhs =
  let case = L1.get_sel_case dts sel in
  let cons = fst case in
  let sels = List.map fst (snd case) in
  let args =
    List.map
      (fun s -> if s.value = sel.value then rhs else L1.Project (s, from))
      sels
  in
  L1.Call (cons, args)

let rec reduce_expr (dts : L1.data_def list) (inp : L1.expr) : L1.expr =
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
  | Do [] -> raise (ReduceUpdateError "Empty DO!")
  | Do [a] -> red a
  | Do (left :: right) -> Do [red left; red (Do right)]
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Assign (Call (x, []), rhs) -> Assign (Call (x, []), red rhs)
  | Assign (Project (sel, from), rhs) ->
      let new_from = red from in
      let new_rhs = reduce_record_update_helper dts sel new_from (red rhs) in
      red (Assign (new_from, new_rhs))
  | Assign (Select (from, index), rhs) ->
      let new_from = red from in
      let new_rhs = L1.Update (new_from, red index, red rhs) in
      red (Assign (new_from, new_rhs))
  | Assign _ as e ->
      raise (ReduceUpdateError (sprintf "Lhs Assign: %s" (L1.show_expr e)))

let reduce_command (dts : L1.data_def list) : L1.command -> L1.command =
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

let reduce_fun (dts : L1.data_def list) (defn0 : L1.fun_def) : L1.fun_def =
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

let reduce (prog : L1.program) : L1.program =
  let new_datatypes = List.map reduce_datatype prog.datatypes in
  let new_funs = List.map (reduce_fun prog.datatypes) prog.funs in
  let new_body = List.map (reduce_command prog.datatypes) prog.body in
  {funs= new_funs; datatypes= new_datatypes; body= new_body}
