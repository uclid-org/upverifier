(** Inline all sort synonyms **)

open Common.Error
open Common
open Common.Suggestion
open Printf

type environment = L2.sort symtab

let rec reduce_sort (sorts : L3.sort_def list) (datatypes : L3.data_def list)
    (env : environment) : L3.sort -> L2.sort = function
  | IntSort -> IntSort
  | BoolSort -> BoolSort
  | StringSort -> StringSort
  | SeqSort a ->
      let new_a = reduce_sort sorts datatypes env a in
      SeqSort new_a
  | ArraySort (inp, out) ->
      let new_in = reduce_sort sorts datatypes env inp in
      let new_out = reduce_sort sorts datatypes env out in
      ArraySort (new_in, new_out)
  | SortCall (f, []) when Symtab.mem f.value env -> Symtab.find f.value env
  | SortCall (f, args) as e when L3.is_sort sorts f ->
      let defn = L3.get_sort sorts f in
      if List.length args = List.length defn.params then
        let fenv =
          args
          |> List.map (reduce_sort sorts datatypes env)
          |> List.combine (List.map (fun p -> p.value) defn.params)
          |> of_list
        in
        reduce_sort sorts datatypes fenv defn.body
      else
        raise
          (ReduceSortError
             (sprintf
                "reduce_sort failed at \"%s\" %s\nNumber of arguments and parameters don't match!"
                (L3.show_sort e) (show_pos f.position) ) )
  | SortCall (f, args) as e when L3.is_data datatypes f ->
      let defn = L3.get_data datatypes f in
      if List.length args = List.length defn.params then
        SortCall (f, List.map (reduce_sort sorts datatypes env) args)
      else
        raise
          (ReduceSortError
             (sprintf
                "reduce_sort failed at \"%s\" %s\nNumber of arguments and parameters don't match!"
                (L3.show_sort e) (show_pos f.position) ) )
  | SortCall (f, []) -> SortCall (f, [])
  | SortCall (f, args) -> (
      let length = List.length args in
      let candidates =
        ( if length = 0 then
          List.of_seq (Seq.map (fun x -> fst x) (to_list env))
        else [] )
        @ List.filter_map
            (fun (x : Smtlib.sort_def) ->
              if List.length x.params = length then Some x.name.value
              else None )
            sorts
        @ List.filter_map
            (fun (x : Smtlib.data_def) ->
              if List.length x.params = length then Some x.name.value
              else None )
            datatypes
        @ ["Bool"; "Int"; "String"; "Array"; "Seq"]
      in
      match suggest candidates f.value with
      | Some best ->
          raise
            (ReduceSortError
               (sprintf "Unknown sort %s\nDid you mean \"%s\"?"
                  (show_pstring f) best ) )
      | None ->
          raise
            (ReduceSortError
               (sprintf "Unknown sort %s\nNo candidates to suggest."
                  (show_pstring f) ) ) )

let rec reduce_expr (sorts : L3.sort_def list) (datatypes : L3.data_def list)
    (env : environment) (inp : L3.expr) : L2.expr =
  let red = reduce_expr sorts datatypes env in
  match inp with
  | Not arg -> Not (red arg)
  | And (a1, a2) -> And (red a1, red a2)
  | Or (a1, a2) -> Or (red a1, red a2)
  | Implies (a1, a2) -> Implies (red a1, red a2)
  | Plus (a1, a2) -> Plus (red a1, red a2)
  | Minus (a1, a2) -> Minus (red a1, red a2)
  | Times (a1, a2) -> Times (red a1, red a2)
  | Concat (a1, a2) -> Concat (red a1, red a2)
  | Eq (a1, a2) -> Eq (red a1, red a2)
  | Is (a1, a2) -> Is (red a1, a2)
  | Prefix (a1, a2) -> Prefix (red a1, red a2)
  | Suffix (a1, a2) -> Suffix (red a1, red a2)
  | Contains (a1, a2) -> Contains (red a1, red a2)
  | Lt (a1, a2) -> Lt (red a1, red a2)
  | Lte (a1, a2) -> Lte (red a1, red a2)
  | Gt (a1, a2) -> Gt (red a1, red a2)
  | Gte (a1, a2) -> Gte (red a1, red a2)
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
  | Length e -> Length (red e)
  | Unit e -> Unit (red e)
  | Const (e, t) -> Const (red e, reduce_sort sorts datatypes env t)
  | As (e, t) -> As (red e, reduce_sort sorts datatypes env t)
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Forall (ps, b) ->
      Forall
        ( List.map (fun (x, s) -> (x, reduce_sort sorts datatypes env s)) ps
        , red b )
  | Exists (ps, b) ->
      Exists
        ( List.map (fun (x, s) -> (x, reduce_sort sorts datatypes env s)) ps
        , red b )
  | Assign (lhs, rhs) -> Assign (red lhs, red rhs)
  | Do [] -> raise (ReduceExprError "Empty DO!")
  | Do [lhs] -> red lhs
  | Do (lhs :: rhs) -> Do [red lhs; red (Do rhs)]

let reduce_command (sorts : L3.sort_def list) (datatypes : L3.data_def list)
    : L3.command -> L2.command = function
  | Check -> Check
  | Push -> Push
  | Pop -> Pop
  | Print (Left e) ->
      Print (Left (reduce_expr sorts datatypes Symtab.empty e))
  | Print (Right e) -> Print (Right e)
  | Assume e -> Assume (reduce_expr sorts datatypes Symtab.empty e)
  | Assert e -> Assert (reduce_expr sorts datatypes Symtab.empty e)
  | Choose ((x, sx), Some (y, sy), a, b) ->
      Choose
        ( (x, reduce_sort sorts datatypes Symtab.empty sx)
        , Some (y, reduce_sort sorts datatypes Symtab.empty sy)
        , Option.map (reduce_expr sorts datatypes Symtab.empty) a
        , Option.map (reduce_expr sorts datatypes Symtab.empty) b )
  | Choose ((x, sx), None, a, b) ->
      Choose
        ( (x, reduce_sort sorts datatypes Symtab.empty sx)
        , None
        , Option.map (reduce_expr sorts datatypes Symtab.empty) a
        , Option.map (reduce_expr sorts datatypes Symtab.empty) b )

let reduce_datatype (sorts : L3.sort_def list) (datatypes : L3.data_def list)
    (d : L3.data_def) : L2.data_def =
  let fenv =
    d.params
    |> List.map (fun x -> L2.SortCall (x, []))
    |> List.combine (List.map (fun p -> p.value) d.params)
    |> of_list
  in
  let new_cases =
    List.map
      (fun (c, sels) ->
        ( c
        , List.map
            (fun (n, s) -> (n, reduce_sort sorts datatypes fenv s))
            sels ) )
      d.cases
  in
  {name= d.name; params= d.params; cases= new_cases}

let reduce_fun (sorts : L3.sort_def list) (datatypes : L3.data_def list)
    (defn0 : L3.fun_def) : L2.fun_def =
  let fenv =
    let sort_keys = List.map (fun x -> x.value) defn0.sort_params in
    let sort_vals =
      List.map (fun x -> L2.SortCall (x, [])) defn0.sort_params
    in
    let paired = List.combine sort_keys sort_vals in
    of_list paired
  in
  let new_params =
    List.map
      (fun (n, s) -> (n, reduce_sort sorts datatypes fenv s))
      defn0.params
  in
  let new_sort = reduce_sort sorts datatypes fenv defn0.sort in
  let new_body =
    Option.map (reduce_expr sorts datatypes Symtab.empty) defn0.body
  in
  { name= defn0.name
  ; recursive= defn0.recursive
  ; sort_params= defn0.sort_params
  ; params= new_params
  ; body= new_body
  ; sort= new_sort }

let reduce (prog : L3.program) : L2.program =
  let new_datatypes =
    List.map (reduce_datatype prog.sorts prog.datatypes) prog.datatypes
  in
  let new_funs = List.map (reduce_fun prog.sorts prog.datatypes) prog.funs in
  let new_body =
    List.map (reduce_command prog.sorts prog.datatypes) prog.body
  in
  {funs= new_funs; datatypes= new_datatypes; body= new_body}
