open L3
open Common.Error
open Common
open Common.Suggestion
open Printf
open Sort

type environment = sort symtab

let typecheck_unary_primitive e arg_type =
  match (e, arg_type) with Not _, BoolSort -> Some BoolSort | _ -> None

let typecheck_binary_primitive e arg1_type arg2_type =
  match (e, arg1_type, arg2_type) with
  | Implies (_, _), BoolSort, BoolSort
   |And (_, _), BoolSort, BoolSort
   |Or (_, _), BoolSort, BoolSort ->
      Some BoolSort
  | Plus (_, _), IntSort, IntSort
   |Times (_, _), IntSort, IntSort
   |Minus (_, _), IntSort, IntSort ->
      Some IntSort
  | Lt (_, _), IntSort, IntSort
   |Lte (_, _), IntSort, IntSort
   |Gt (_, _), IntSort, IntSort
   |Gte (_, _), IntSort, IntSort ->
      Some BoolSort
  | _ -> None

let rec typecheck_term (funs : fun_def list) (sorts : sort_def list)
    (datatypes : data_def list) (sort_env : environment)
    (var_env : environment) (inp : expr) : sort =
  let tc_term = typecheck_term funs sorts datatypes sort_env var_env in
  let out =
    match inp with
    | Num _ -> IntSort
    | Str _ -> StringSort
    | Call (var, []) when Symtab.mem var.value var_env ->
        Symtab.find var.value var_env
    | Let (var, exp, body) ->
        let fvar_env = var_env |> Symtab.add var.value (tc_term exp) in
        typecheck_term funs sorts datatypes sort_env fvar_env body
    | If (test_exp, then_exp, else_exp) as e ->
        let test_sort = tc_term test_exp in
        let then_sort = tc_term then_exp in
        let else_sort = tc_term else_exp in
        let body_sort = matching_sort then_sort else_sort in
        if Option.is_none (matching_sort test_sort BoolSort) then
          raise
            (TypeMismatch
               (sprintf
                  "If test must be \"Bool\" but is \"%s\" for expression \"%s\""
                  (show_sort test_sort) (show_expr test_exp) ) ) ;
        if Option.is_some body_sort then Option.get body_sort
        else
          raise
            (TypeMismatch
               (sprintf
                  "If branches must be of same type!\n\t%s\nThen branch has type %s; else branch has type %s"
                  (show_expr e) (show_sort then_sort) (show_sort else_sort) )
            )
    | Call (f, args) as e when is_fun funs f ->
        let defn = get_fun funs f in
        if List.length args = List.length defn.params then (
          let param_sorts = snd (List.split defn.params) in
          let arg_sorts = List.map tc_term args in
          List.iteri
            (fun i (a, b) ->
              let a = unify sorts datatypes param_sorts arg_sorts a in
              let b = unify sorts datatypes param_sorts arg_sorts b in
              if Option.is_none (matching_sort a b) then
                raise
                  (TypeMismatch
                     (sprintf
                        "Argument number %d of sort \"%s\" for call %s\ndoes not match parameter \"%s\" of sort \"%s\" %s"
                        (i + 1) (show_sort a) (show_pstring f)
                        (List.nth (fst (List.split defn.params)) i).value
                        (show_sort b)
                        (show_pos
                           (List.nth (fst (List.split defn.params)) i)
                             .position ) ) ) )
            (List.combine arg_sorts param_sorts) ;
          let to_fill = defn.sort in
          unify sorts datatypes param_sorts arg_sorts to_fill )
        else
          raise
            (TypeMismatch
               (sprintf
                  "Number of arguments (%d) does not match number of parameters (%d) in call %s %s\nDefined at %s"
                  (List.length args) (List.length defn.params) (show_expr e)
                  (show_pstring f) (show_pstring defn.name) ) )
    | Call (f, args) as e when is_cons datatypes f ->
        let defn = get_cons_defn datatypes f in
        let case = get_cons_case datatypes f in
        let sels = snd case in
        if List.length args = List.length sels then (
          let param_sorts = snd (List.split sels) in
          let arg_sorts = List.map tc_term args in
          List.iteri
            (fun i (a, b) ->
              let a = unify sorts datatypes param_sorts arg_sorts a in
              let b = unify sorts datatypes param_sorts arg_sorts b in
              if Option.is_none (matching_sort a b) then
                raise
                  (TypeMismatch
                     (sprintf
                        "Argument number %d of sort \"%s\" for call %s\ndoes not match parameter \"%s\" of sort \"%s\" %s"
                        (i + 1) (show_sort a) (show_pstring f)
                        (List.nth (fst (List.split sels)) i).value
                        (show_sort b)
                        (show_pos
                           (List.nth (fst (List.split sels)) i).position ) )
                  ) )
            (List.combine arg_sorts param_sorts) ;
          let to_fill =
            SortCall
              (defn.name, List.map (fun x -> SortCall (x, [])) defn.params)
          in
          unify sorts datatypes param_sorts arg_sorts to_fill )
        else
          raise
            (TypeMismatch
               (sprintf
                  "Number of arguments (%d) does not match number of parameters (%d) in call %s %s\nDefined at %s"
                  (List.length args) (List.length sels) (show_expr e)
                  (show_pstring f)
                  (show_pstring (fst case)) ) )
    | Call (f, args) -> (
        let length = List.length args in
        let candidates =
          ( if length = 0 then
            List.of_seq (Seq.map (fun x -> fst x) (to_list var_env))
          else [] )
          @ List.filter_map
              (fun x ->
                if List.length x.params = length then Some x.name.value
                else None )
              funs
          @ List.flatten
              (List.map
                 (fun x ->
                   List.filter_map
                     (fun y ->
                       if List.length (snd y) = length then
                         Some (fst y).value
                       else None )
                     x.cases )
                 datatypes )
        in
        match suggest candidates f.value with
        | Some best ->
            raise
              (TypeMismatch
                 (sprintf "Unknown function %s\nDid you mean \"%s\"?"
                    (show_pstring f) best ) )
        | None ->
            raise
              (TypeMismatch
                 (sprintf "Unknown function %s\nNo candidates to suggest."
                    (show_pstring f) ) ) )
    | Project (f, arg) as e when is_sel datatypes f -> (
        let v = tc_term arg in
        match v with
        | SortCall (dt, _) when is_data datatypes dt ->
            let defn = get_data datatypes dt in
            let to_fill =
              if is_sel [defn] f then get_sel_sort [defn] f
              else
                raise
                  (TypeMismatch
                     (sprintf "Unknown selector %s" (show_pstring f)) )
            in
            let templates =
              [ SortCall
                  (dt, List.map (fun x -> SortCall (x, [])) defn.params) ]
            in
            let data = [v] in
            unify sorts datatypes templates data to_fill
        | s when List.length (get_params sorts datatypes s) = 1 ->
            (* If it is a param, then it can be literally any type (unless
               this projection is used again on the same type... I guess the
               type system just won't be complete...) *)
            SortCall ({value= gensym "UnknownType"; position= f.position}, [])
        | s ->
            raise
              (TypeMismatch
                 (sprintf "Expected datatype but got \"%s\" at %s %s"
                    (show_sort s) (show_expr e) (show_pstring f) ) ) )
    | Project (f, _) -> (
        let candidates =
          List.flatten
            (List.map
               (fun d ->
                 List.flatten
                   (List.map
                      (fun (_, sels) -> List.map (fun (n, _) -> n.value) sels)
                      d.cases ) )
               datatypes )
        in
        match suggest candidates f.value with
        | Some best ->
            raise
              (TypeMismatch
                 (sprintf "Unknown selector %s\nDid you mean \"%s\"?"
                    (show_pstring f) best ) )
        | None ->
            raise
              (TypeMismatch
                 (sprintf "Unknown selector %s\nNo candidates to suggest."
                    (show_pstring f) ) ) )
    | Select (from, index) as e -> (
        let from_t = tc_term from in
        let index_t = tc_term index in
        match from_t with
        | ArraySort (inp, out) as s ->
            let a = unify sorts datatypes [inp] [index_t] index_t in
            let b = unify sorts datatypes [inp] [a] inp in
            if Option.is_some (matching_sort a b) then out
            else
              raise
                (TypeMismatch
                   (sprintf
                      "Select \"%s\" failed! Tried to select from an expression of sort \"%s\" but need an array with index sort \"%s\""
                      (show_expr e) (show_sort s) (show_sort index_t) ) )
        | s ->
            raise
              (TypeMismatch
                 (sprintf
                    "Select \"%s\" failed! Tried to select from an expression of sort \"%s\" but need an array with index sort \"%s\""
                    (show_expr e) (show_sort s) (show_sort index_t) ) ) )
    | Not arg as e -> (
        let arg_type = tc_term arg in
        match typecheck_unary_primitive e arg_type with
        | Some BoolSort -> BoolSort
        | Some v ->
            raise
              (TypeMismatch
                 (sprintf "Expected %s but got %s at %s" (show_sort BoolSort)
                    (show_sort v) (show_expr e) ) )
        | None ->
            raise
              (TypeMismatch
                 (sprintf "Expected %s but could not infer type at %s"
                    (show_sort BoolSort) (show_expr e) ) ) )
    | Eq (arg1, arg2) as e ->
        let a = tc_term arg1 in
        let b = tc_term arg2 in
        let a = unify sorts datatypes [b] [a] a in
        let b = unify sorts datatypes [b] [a] b in
        if Option.is_some (matching_sort a b) then BoolSort
        else
          raise
            (TypeMismatch
               (sprintf
                  "Equality sorts not compatible! %s is attempting to compare an element of %s with an element of %s"
                  (show_expr e) (show_sort a) (show_sort b) ) )
    | Concat (a, b) as e -> (
        let a = tc_term a in
        let b = tc_term b in
        let a = unify sorts datatypes [b] [a] a in
        let b = unify sorts datatypes [b] [a] b in
        match matching_sort a b with
        | Some (SeqSort v) -> SeqSort v
        | _ ->
            raise
              (TypeMismatch
                 (sprintf
                    "Concat sorts not compatible! %s is attempting to concat an element of %s with an element of %s"
                    (show_expr e) (show_sort a) (show_sort b) ) ) )
    | (Prefix (a, b) | Suffix (a, b) | Contains (a, b)) as e -> (
        let a = tc_term a in
        let b = tc_term b in
        let a = unify sorts datatypes [b] [a] a in
        let b = unify sorts datatypes [b] [a] b in
        match matching_sort a b with
        | Some (SeqSort _) -> BoolSort
        | _ ->
            raise
              (TypeMismatch
                 (sprintf
                    "Concat sorts not compatible! %s is attempting to concat an element of %s with an element of %s"
                    (show_expr e) (show_sort a) (show_sort b) ) ) )
    | ( And (arg1, arg2)
      | Or (arg1, arg2)
      | Implies (arg1, arg2)
      | Plus (arg1, arg2)
      | Times (arg1, arg2)
      | Minus (arg1, arg2)
      | Lt (arg1, arg2)
      | Lte (arg1, arg2)
      | Gt (arg1, arg2)
      | Gte (arg1, arg2) ) as e -> (
        let t1 = tc_term arg1 in
        let t2 = tc_term arg2 in
        match typecheck_binary_primitive e t1 t2 with
        | Some v -> v
        | None ->
            raise
              (TypeMismatch
                 (sprintf
                    "Argument types should match but don't at %s. Left-hand-side is of sort %s; right-hand-side is of sort %s."
                    (show_expr e) (show_sort t1) (show_sort t2) ) ) )
    | True -> BoolSort
    | False -> BoolSort
    | As (v, s) as e ->
        let vt = tc_term v in
        let tt = eval_sort sorts datatypes sort_env s in
        let a = unify sorts datatypes [vt] [tt] tt in
        let b = unify sorts datatypes [vt] [a] vt in
        if Option.is_some (matching_sort a b) then a
        else
          raise
            (TypeMismatch
               (sprintf "As call \"%s\" must match! Got \"%s\" and \"%s\""
                  (show_expr e) (show_sort vt) (show_sort tt) ) )
    | Length s as e -> (
      match tc_term s with
      | SeqSort _ -> IntSort
      | t ->
          raise
            (TypeMismatch
               (sprintf "Length call \"%s\" must be a sequence! Got \"%s\""
                  (show_expr e) (show_sort t) ) ) )
    | Unit e ->
        let t = tc_term e in
        SeqSort t
    | Const (v, s) as e -> (
        let et = tc_term v in
        match eval_sort sorts datatypes sort_env s with
        | ArraySort (_, out) when Option.is_some (matching_sort et out) -> s
        | _ ->
            raise
              (TypeMismatch
                 (sprintf
                    "Const call \"%s\": \"%s\" must be an ArraySort and \"%s\" must be the element type of \"%s\"!"
                    (show_expr e) (show_sort s) (show_expr v) (show_sort s) )
              ) )
    | Update (from, index, plug) as e -> (
        let new_from = tc_term from in
        let new_index = tc_term index in
        let new_plug = tc_term plug in
        match new_from with
        | ArraySort (inp, out) ->
            if Option.is_none (matching_sort new_index inp) then
              raise
                (TypeMismatch
                   (sprintf
                      "Index type for array update does not match at \"%s\"! Expected \"%s\" but got \"%s\""
                      (show_expr e) (show_sort new_index) (show_sort inp) )
                ) ;
            if Option.is_some (matching_sort new_plug out) then new_from
            else
              raise
                (TypeMismatch
                   (sprintf "Element type does not match! %s" (show_expr e))
                )
        | s ->
            raise
              (TypeMismatch
                 (sprintf "Must index from an array, not a %s. Problem at %s"
                    (show_sort s) (show_expr e) ) ) )
    | Is (arg1, f) as e when is_cons datatypes f -> (
      match
        let t1 = tc_term arg1 in
        let defn = get_cons_defn datatypes f in
        let t2 =
          SortCall
            (defn.name, List.map (fun x -> SortCall (x, [])) defn.params)
        in
        ( unify sorts datatypes [t1] [t2] t1
        , unify sorts datatypes [t1] [t2] t2 )
      with
      | a, b when Option.is_some (matching_sort a b) -> BoolSort
      | _ -> raise (TypeMismatch (show_expr e)) )
    | Is (_, f) -> (
        let candidates =
          List.flatten
            (List.map
               (fun x ->
                 List.filter_map
                   (fun y ->
                     if List.length (snd y) = 0 then Some (fst y).value
                     else None )
                   x.cases )
               datatypes )
          @ List.of_seq (Seq.map (fun x -> fst x) (to_list var_env))
          @ List.map (fun x -> x.name.value) funs
        in
        match suggest candidates f.value with
        | Some best ->
            raise
              (TypeMismatch
                 (sprintf
                    "Second argument of instance check must be a constructor %s\nDid you mean \"%s\"?"
                    (show_pos f.position) best ) )
        | None ->
            raise
              (TypeMismatch
                 (sprintf
                    "Second argument of instance check must be a constructor %s\nNo candidates to suggest."
                    (show_pos f.position) ) ) )
    | Forall (params, body) as e -> (
        let fvar_env =
          List.fold_left
            (fun acc (n, s) -> Symtab.add n s acc)
            var_env
            (List.map (fun (a, s) -> (a.value, s)) params)
        in
        match typecheck_term funs sorts datatypes sort_env fvar_env body with
        | BoolSort -> BoolSort
        | v ->
            raise
              (TypeMismatch
                 (sprintf "Expected %s but got %s at %s" (show_sort BoolSort)
                    (show_sort v) (show_expr e) ) ) )
    | Exists (params, body) as e -> (
        let fvar_env =
          List.fold_left
            (fun acc (n, s) -> Symtab.add n s acc)
            var_env
            (List.map (fun (a, s) -> (a.value, s)) params)
        in
        match typecheck_term funs sorts datatypes sort_env fvar_env body with
        | BoolSort -> BoolSort
        | v ->
            raise
              (TypeMismatch
                 (sprintf "Expected %s but got %s at %s" (show_sort BoolSort)
                    (show_sort v) (show_expr e) ) ) )
    | Assign (lhs, rhs) -> (
        let _ = tc_term rhs in
        match lhs with
        | Call (_, []) as e -> tc_term e
        | Select (from, _) as e ->
            let _ = tc_term e in
            tc_term (Assign (from, from))
        | Project (_, from) as e ->
            let _ = tc_term e in
            tc_term (Assign (from, from))
        | _ as e ->
            raise
              (TypeMismatch
                 (sprintf
                    "Left-hand-side of assignments must be a variable, an array select, or a record project. Got %s."
                    (show_expr e) ) ) )
    | Do [] -> raise (TypeMismatch "Empty DO!")
    | Do (head :: tail) ->
        let _ =
          match head with
          | Assign (_, _) as e -> tc_term e
          | If (_, _, _) as e ->
              tc_term e (* TODO: check that left and right match? *)
          | _ as e ->
              raise
                (TypeMismatch
                   (sprintf "Head of do-pairs must be an assignment. Got %s."
                      (show_expr e) ) )
        in
        List.hd (List.rev_map tc_term tail)
  in
  eval_sort sorts datatypes sort_env out
