(** Support parametric functions **)

open Common
open Common.Error
open Check
open L2

type environment = L1.sort symtab

let instances_todo = ref []

let instances_done = ref []

let rec infer_sort (funs : fun_def list) (datatypes : data_def list)
    (var_env : sort symtab) : expr -> sort = function
  | Implies _ | And _ | Or _ | Not _ | Eq _ | Is _ | Lt _ | Lte _ | Gt _
   |Exists _ | Forall _ | True | False | Gte _ | Prefix _ | Suffix _
   |Contains _ ->
      BoolSort
  | Num _ | Plus _ | Minus _ | Times _ -> IntSort
  | Str _ -> StringSort
  | Do [] -> raise (Stuck "Empty DO!")
  | Do (body :: _) | Assign (body, _) | If (_, body, _) | Update (body, _, _)
    ->
      infer_sort funs datatypes var_env body
  | Let (var, exp, body) ->
      let env =
        var_env
        |> Symtab.add var.value (infer_sort funs datatypes var_env exp)
      in
      infer_sort funs datatypes env body
  | Concat (a, _) -> infer_sort funs datatypes var_env a
  | Length _ -> IntSort
  | Unit e -> SeqSort (infer_sort funs datatypes var_env e)
  | Const (_, s) -> s
  | As (_, s) -> s
  | Call (var, []) when Symtab.mem var.value var_env ->
      let arg_type = Symtab.find var.value var_env in
      arg_type
  | Call (f, args) when is_fun funs f ->
      let defn = get_fun funs f in
      let param_sorts = snd (List.split defn.params) in
      let arg_sorts = List.map (infer_sort funs datatypes var_env) args in
      let to_fill = defn.sort in
      unify [] datatypes param_sorts arg_sorts to_fill
  | Call (f, args) ->
      (* Must be a constructor if not a fun *)
      let defn = get_cons_defn datatypes f in
      let case = get_cons_case datatypes f in
      let sels = snd case in
      let param_sorts = snd (List.split sels) in
      let arg_sorts = List.map (infer_sort funs datatypes var_env) args in
      let to_fill =
        SortCall (defn.name, List.map (fun x -> SortCall (x, [])) defn.params)
      in
      unify [] datatypes param_sorts arg_sorts to_fill
  | Project (f, body) ->
      let defn = get_sel_defn datatypes f in
      let sel_sort = get_sel_sort datatypes f in
      let param_sorts =
        [ SortCall
            (defn.name, List.map (fun x -> SortCall (x, [])) defn.params) ]
      in
      let arg_sorts = [infer_sort funs datatypes var_env body] in
      let to_fill = sel_sort in
      unify [] datatypes param_sorts arg_sorts to_fill
  | Select (from, _) as e -> (
    match infer_sort funs datatypes var_env from with
    | ArraySort (_, out) -> out
    | _ -> raise (Stuck (Printf.sprintf "Failed select: %s\n" (show_expr e)))
    )

let reduce_sort (inp : sort) : L1.sort = inp

let reduce_datatype (inp : data_def) : L1.data_def = inp

let rec reduce_expr ctx (funs : fun_def list) (datatypes : data_def list)
    (var_env : sort symtab) (inp : expr) : L1.expr =
  let red = reduce_expr ctx funs datatypes var_env in
  match inp with
  | True -> True
  | False -> False
  | Num v -> Num v
  | Str v -> Str v
  | Let (var, exp, body) ->
      let env =
        var_env
        |> Symtab.add var.value (infer_sort funs datatypes var_env exp)
      in
      Let
        ( var
        , reduce_expr ctx funs datatypes env exp
        , reduce_expr ctx funs datatypes env body )
  | If (test_exp, then_exp, else_exp) ->
      If (red test_exp, red then_exp, red else_exp)
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
  | Const (e, t) -> Const (red e, reduce_sort (ctx t))
  | As (e, t) -> As (red e, reduce_sort (ctx t))
  | Forall (ps, b) ->
      let params = List.map (fun (x, y) -> (x, reduce_sort y)) ps in
      let env =
        List.fold_left
          (fun acc (x, y) -> Symtab.add x.value (reduce_sort y) acc)
          var_env params
      in
      Forall (params, reduce_expr ctx funs datatypes env b)
  | Exists (ps, b) ->
      let params = List.map (fun (x, y) -> (x, reduce_sort y)) ps in
      let env =
        List.fold_left
          (fun acc (x, y) -> Symtab.add x.value (reduce_sort y) acc)
          var_env params
      in
      Exists (params, reduce_expr ctx funs datatypes env b)
  | Do [] -> raise (Stuck "Empty DO!")
  | Do [left] -> red left
  | Do (left :: right) -> Do [red left; red (Do right)]
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Assign (lhs, rhs) -> Assign (red lhs, red rhs)
  | Call (f, args)
    when is_fun funs f && List.length (get_fun funs f).sort_params > 0 ->
      let defn = get_fun funs f in
      let param_sorts = snd (List.split defn.params) in
      let arg_sorts = List.map (infer_sort funs datatypes var_env) args in
      let bindings =
        List.map
          (fun (a, b) -> (a, unify [] datatypes param_sorts arg_sorts b))
          defn.params
      in
      instances_todo := (defn.name, bindings) :: !instances_todo ;
      Call (f, List.map red args)
  | Call (f, args) -> Call (f, List.map red args)

let reduce_command (funs : fun_def list) (datatypes : data_def list) :
    command -> L1.command = function
  | Check -> Check
  | Push -> Push
  | Pop -> Pop
  | Print (Left e) ->
      Print (Left (reduce_expr (fun x -> x) funs datatypes Symtab.empty e))
  | Print (Right e) -> Print (Right e)
  | Assume e ->
      Assume (reduce_expr (fun x -> x) funs datatypes Symtab.empty e)
  | Assert e ->
      Assert (reduce_expr (fun x -> x) funs datatypes Symtab.empty e)
  | Choose ((x, sx), Some (y, sy), a, b) ->
      Choose
        ( (x, reduce_sort sx)
        , Some (y, reduce_sort sy)
        , Option.map (reduce_expr (fun x -> x) funs datatypes Symtab.empty) a
        , Option.map (reduce_expr (fun x -> x) funs datatypes Symtab.empty) b
        )
  | Choose ((x, sx), None, a, b) ->
      Choose
        ( (x, reduce_sort sx)
        , None
        , Option.map (reduce_expr (fun x -> x) funs datatypes Symtab.empty) a
        , Option.map (reduce_expr (fun x -> x) funs datatypes Symtab.empty) b
        )

let reduce_fun (funs : fun_def list) (datatypes : data_def list)
    (defn : fun_def) : L1.fun_def =
  let env : sort symtab =
    of_list (List.map (fun (x, s) -> (x.value, s)) defn.params)
  in
  let new_params =
    List.map (fun (x, s) -> (x, eval_sort [] datatypes env s)) defn.params
  in
  let new_body =
    Option.map (reduce_expr (fun x -> x) funs datatypes env) defn.body
  in
  let new_sort = eval_sort [] datatypes env defn.sort in
  let old_param_sorts = snd (List.split defn.params) in
  let new_param_sorts = snd (List.split new_params) in
  let to_fill = new_sort in
  let new_sort =
    unify [] datatypes old_param_sorts new_param_sorts to_fill
  in
  { name= defn.name
  ; recursive= defn.recursive
  ; params= new_params
  ; body= new_body
  ; sort= new_sort }

let instantiate_fun (funs : fun_def list) (datatypes : data_def list) pairs :
    fun_def =
  let f, new_params = pairs in
  let defn = get_fun funs f in
  let env : sort symtab =
    of_list (List.map (fun (x, s) -> (x.value, s)) new_params)
  in
  let new_sort = eval_sort [] datatypes env defn.sort in
  let old_param_sorts = snd (List.split defn.params) in
  let new_param_sorts = snd (List.split new_params) in
  let to_fill = new_sort in
  let new_sort =
    unify [] datatypes old_param_sorts new_param_sorts to_fill
  in
  let new_body =
    Option.map
      (reduce_expr
         (unify [] datatypes old_param_sorts new_param_sorts)
         funs datatypes env )
      defn.body
  in
  { name= f
  ; recursive= defn.recursive
  ; sort_params=
      List.flatten
        (List.map
           (Check.get_params [] datatypes)
           (snd (List.split new_params)) )
  ; params= new_params
  ; body= new_body
  ; sort= new_sort }

let reduce (prog : program) : L1.program =
  instances_todo := [] ;
  instances_done := [] ;
  let funs_with_chooses = get_funs_from_commands prog.body @ prog.funs in
  let new_datatypes = List.map reduce_datatype prog.datatypes in
  let new_body =
    List.map (reduce_command funs_with_chooses prog.datatypes) prog.body
  in
  (* Make sure to visit all functions to get the instances_todo from inside
     them *)
  let _ =
    List.map (reduce_fun funs_with_chooses prog.datatypes) funs_with_chooses
  in
  let new_funs = ref [] in
  while List.length !instances_todo > 0 do
    match !instances_todo with
    | i :: _ ->
        instances_todo := List.tl !instances_todo ;
        let string_i =
          ( (fst i).value
          , List.map (fun (a, b) -> (a.value, show_sort b)) (snd i) )
        in
        if List.mem string_i !instances_done then ()
        else (
          instances_done := string_i :: !instances_done ;
          let new_fun = instantiate_fun funs_with_chooses prog.datatypes i in
          let _ = reduce_fun funs_with_chooses prog.datatypes new_fun in
          new_funs := new_fun :: !new_funs )
    | _ -> ()
  done ;
  let new_funs =
    List.filter
      (fun (d : fun_def) -> List.length d.sort_params = 0)
      (prog.funs @ List.rev !new_funs)
  in
  let new_funs =
    List.map (reduce_fun funs_with_chooses prog.datatypes) new_funs
  in
  {funs= new_funs; datatypes= new_datatypes; body= new_body}
