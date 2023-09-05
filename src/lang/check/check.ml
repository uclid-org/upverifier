open L3
open Common
open Common.Error
open Common.Suggestion
open Term
open Command
open Printf
open Sort

let rec has_duplicate_function_names (reference : fun_def list)
    (checklist : fun_def list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_opt
        (fun (a : fun_def) -> a <> x && a.name.value = x.name.value)
        reference
    with
    | Some e -> Some (x.name, e.name)
    | None -> has_duplicate_function_names reference xs )

let rec has_duplicate_sort_names (reference : sort_def list)
    (checklist : sort_def list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_opt
        (fun (a : sort_def) -> a <> x && a.name.value = x.name.value)
        reference
    with
    | Some e -> Some (x.name, e.name)
    | None -> has_duplicate_sort_names reference xs )

let rec has_duplicate_datatype_names (reference : data_def list)
    (checklist : data_def list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_opt
        (fun (a : data_def) -> a <> x && a.name.value = x.name.value)
        reference
    with
    | Some e -> Some (x.name, e.name)
    | None -> has_duplicate_datatype_names reference xs )

let rec has_duplicate_cons_helper
    (reference : (pstring * (pstring * sort) list) list)
    (checklist : (pstring * (pstring * sort) list) list) :
    (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_opt
        (fun (a : pstring * (pstring * sort) list) ->
          (fst a).value = (fst x).value
          && (fst a).position <> (fst x).position )
        reference
    with
    | None -> has_duplicate_cons_helper reference xs
    | Some v -> Some (fst x, fst v) )

let rec has_duplicate_cons (reference : data_def list)
    (checklist : data_def list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_map
        (fun (a : data_def) -> has_duplicate_cons_helper a.cases x.cases)
        reference
    with
    | Some e -> Some e
    | None -> has_duplicate_cons reference xs )

let rec has_duplicate_sel_helper2 (reference : (pstring * sort) list)
    (checklist : (pstring * sort) list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_opt
        (fun (a : pstring * sort) ->
          (fst a).value = (fst x).value
          && (fst a).position <> (fst x).position )
        reference
    with
    | None -> has_duplicate_sel_helper2 reference xs
    | Some y -> Some (fst x, fst y) )

let rec has_duplicate_sel_helper
    (reference : (pstring * (pstring * sort) list) list)
    (checklist : (pstring * (pstring * sort) list) list) :
    (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_map
        (fun (a : pstring * (pstring * sort) list) ->
          has_duplicate_sel_helper2 (snd a) (snd x) )
        reference
    with
    | None -> has_duplicate_sel_helper reference xs
    | Some v -> Some v )

let rec has_duplicate_sel (reference : data_def list)
    (checklist : data_def list) : (pstring * pstring) option =
  match checklist with
  | [] -> None
  | x :: xs -> (
    match
      List.find_map
        (fun (a : data_def) -> has_duplicate_sel_helper a.cases x.cases)
        reference
    with
    | Some e -> Some e
    | None -> has_duplicate_sel reference xs )

let check_fun funs sorts datatypes (defn : fun_def) : unit =
  List.iter
    (fun (_, s) ->
      let holes = get_params sorts datatypes s in
      List.iter
        (fun p ->
          if List.mem p.value (List.map (fun x -> x.value) defn.sort_params)
          then ()
          else
            let candidates =
              List.map (fun p -> p.value) defn.sort_params
              @ List.filter_map
                  (fun (x : sort_def) ->
                    if List.length x.params = 0 then Some x.name.value
                    else None )
                  sorts
              @ List.filter_map
                  (fun (x : data_def) ->
                    if List.length x.params = 0 then Some x.name.value
                    else None )
                  datatypes
              @ ["Bool"; "Int"; "String"; "Array"; "Seq"]
            in
            match suggest candidates p.value with
            | Some best ->
                raise
                  (TypeMismatch
                     (sprintf "Unknown sort %s\nDid you mean \"%s\"?"
                        (show_pstring p) best ) )
            | None ->
                raise
                  (TypeMismatch
                     (sprintf "Unknown sort %s\nNo candidates to suggest."
                        (show_pstring p) ) ) )
        holes )
    defn.params ;
  let sorts_tab =
    of_list
      (List.map (fun p -> (p.value, SortCall (p, []))) defn.sort_params)
  in
  let params_tab =
    of_list
      (List.map
         (fun (p, s) -> (p.value, eval_sort sorts datatypes sorts_tab s))
         defn.params )
  in
  let funs =
    if defn.recursive then funs else List.filter (fun f -> f <> defn) funs
  in
  let expected = eval_sort sorts datatypes sorts_tab defn.sort in
  let actual =
    match defn.body with
    | Some body ->
        typecheck_term funs sorts datatypes sorts_tab params_tab body
    | None -> expected
  in
  if Option.is_none (matching_sort actual expected) then
    raise
      (TypeMismatch
         (Printf.sprintf
            "Expected a return sort of %s but got a return sort of %s for function %s"
            (show_sort expected) (show_sort actual) (show_pstring defn.name) )
      )

let check_datatype sorts datatypes (defn : data_def) : unit =
  List.iter
    (fun (_, sels) ->
      List.iter
        (fun (_, s) ->
          let holes = get_params sorts datatypes s in
          List.iter
            (fun p ->
              if List.mem p.value (List.map (fun x -> x.value) defn.params)
              then ()
              else
                let candidates =
                  List.map (fun p -> p.value) defn.params
                  @ List.filter_map
                      (fun (x : sort_def) ->
                        if List.length x.params = 0 then Some x.name.value
                        else None )
                      sorts
                  @ List.filter_map
                      (fun (x : data_def) ->
                        if List.length x.params = 0 then Some x.name.value
                        else None )
                      datatypes
                  @ ["Bool"; "Int"; "String"; "Array"; "Seq"]
                in
                match suggest candidates p.value with
                | Some best ->
                    raise
                      (TypeMismatch
                         (sprintf "Unknown sort %s\nDid you mean \"%s\"?"
                            (show_pstring p) best ) )
                | None ->
                    raise
                      (TypeMismatch
                         (sprintf
                            "Unknown sort %s\nNo candidates to suggest."
                            (show_pstring p) ) ) )
            holes )
        sels )
    defn.cases

let check (interp : bool) (prog : program) : unit =
  let funs_with_chooses = get_funs_from_commands prog.body @ prog.funs in
  let dup_funs =
    has_duplicate_function_names funs_with_chooses funs_with_chooses
  in
  ( match dup_funs with
  | Some (a, b) ->
      raise
        (DeclarationError
           (sprintf "Duplicate function names\n%s\n%s" (show_pstring a)
              (show_pstring b) ) )
  | None -> () ) ;
  let dup_sorts = has_duplicate_sort_names prog.sorts prog.sorts in
  ( match dup_sorts with
  | Some (a, b) ->
      raise
        (DeclarationError
           (sprintf "Duplicate sort names\n%s\n%s" (show_pstring a)
              (show_pstring b) ) )
  | None -> () ) ;
  let dup_datas =
    has_duplicate_datatype_names prog.datatypes prog.datatypes
  in
  ( match dup_datas with
  | Some (a, b) ->
      raise
        (DeclarationError
           (sprintf "Duplicate datatype names\n%s\n%s" (show_pstring a)
              (show_pstring b) ) )
  | None -> () ) ;
  let dup_cons = has_duplicate_cons prog.datatypes prog.datatypes in
  ( match dup_cons with
  | Some (a, b) ->
      raise
        (DeclarationError
           (sprintf "Duplicate constructor names\n%s\n%s" (show_pstring a)
              (show_pstring b) ) )
  | None -> () ) ;
  let dup_sels = has_duplicate_sel prog.datatypes prog.datatypes in
  ( match dup_sels with
  | Some (a, b) ->
      raise
        (DeclarationError
           (sprintf "Duplicate selector names\n%s\n%s" (show_pstring a)
              (show_pstring b) ) )
  | None -> () ) ;
  List.iter (check_datatype prog.sorts prog.datatypes) prog.datatypes ;
  List.iter (check_fun funs_with_chooses prog.sorts prog.datatypes) prog.funs ;
  List.iter
    (typecheck_command interp funs_with_chooses prog.sorts prog.datatypes
       Symtab.empty )
    prog.body

let unify = Sort.unify

let eval_sort = Sort.eval_sort

let get_params = Sort.get_params
