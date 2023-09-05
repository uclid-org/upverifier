open L3
open Common.Error
open Common
open Common.Suggestion
open Printf

type environment = sort symtab

let rec eval_sort (sorts : sort_def list) (datatypes : data_def list)
    (env : environment) : sort -> sort = function
  | IntSort -> IntSort
  | BoolSort -> BoolSort
  | StringSort -> StringSort
  | SeqSort a ->
      let new_a = eval_sort sorts datatypes env a in
      SeqSort new_a
  | ArraySort (inp, out) ->
      let new_in = eval_sort sorts datatypes env inp in
      let new_out = eval_sort sorts datatypes env out in
      ArraySort (new_in, new_out)
  | SortCall (f, []) when Symtab.mem f.value env -> Symtab.find f.value env
  | SortCall (f, args) as e when is_sort sorts f ->
      let defn = get_sort sorts f in
      if List.length args = List.length defn.params then
        let fenv =
          args
          |> List.map (eval_sort sorts datatypes env)
          |> List.combine (List.map (fun p -> p.value) defn.params)
          |> of_list
        in
        eval_sort sorts datatypes fenv defn.body
      else
        raise
          (ReduceSortError
             (sprintf
                "eval_sort failed at \"%s\" %s\nNumber of arguments and parameters don't match!"
                (show_sort e) (show_pos f.position) ) )
  | SortCall (f, args) as e when is_data datatypes f ->
      let defn = get_data datatypes f in
      if List.length args = List.length defn.params then
        SortCall (f, List.map (eval_sort sorts datatypes env) args)
      else
        raise
          (ReduceSortError
             (sprintf
                "eval_sort failed at \"%s\" %s\nNumber of arguments and parameters don't match!"
                (show_sort e) (show_pos f.position) ) )
  | SortCall (f, []) -> SortCall (f, [])
  | SortCall (f, args) -> (
      let length = List.length args in
      let candidates =
        ( if length = 0 then
          List.of_seq (Seq.map (fun x -> fst x) (to_list env))
        else [] )
        @ List.filter_map
            (fun (x : sort_def) ->
              if List.length x.params = length then Some x.name.value
              else None )
            sorts
        @ List.filter_map
            (fun (x : data_def) ->
              if List.length x.params = length then Some x.name.value
              else None )
            datatypes
        @ ["Bool"; "Int"; "String"; "Array"; "Seq"]
      in
      match suggest candidates f.value with
      | Some best ->
          raise
            (TypeMismatch
               (sprintf "Unknown sort %s\nDid you mean \"%s\"?"
                  (show_pstring f) best ) )
      | None ->
          raise
            (TypeMismatch
               (sprintf "Unknown sort %s\nNo candidates to suggest."
                  (show_pstring f) ) ) )

let rec matching_sort (a : sort) (b : sort) : sort option =
  match (a, b) with
  | IntSort, IntSort -> Some IntSort
  | BoolSort, BoolSort -> Some BoolSort
  | StringSort, StringSort -> Some StringSort
  | SeqSort a, SeqSort b -> (
    match matching_sort a b with
    | Some matched -> Some (SeqSort matched)
    | None -> None )
  | ArraySort (a, b), ArraySort (c, d) ->
      let left = matching_sort a c in
      let right = matching_sort b d in
      if Option.is_some left && Option.is_some right then
        Some (ArraySort (Option.get left, Option.get right))
      else None
  | SortCall (f, []), other
    when String.length f.value > 13
         && String.sub f.value 0 13 = "UnknownType__" ->
      Some other
  | other, SortCall (f, [])
    when String.length f.value > 13
         && String.sub f.value 0 13 = "UnknownType__" ->
      Some other
  | SortCall (f, xs), SortCall (g, ys) when List.length xs = List.length ys
    ->
      let args = List.map2 (fun x y -> matching_sort x y) xs ys in
      if f.value = g.value && List.for_all (fun x -> Option.is_some x) args
      then Some (SortCall (f, List.map (fun x -> Option.get x) args))
      else None
  | _ -> None

let compare_sort x y = match matching_sort x y with Some _ -> 0 | _ -> -1

let rec get_bindings_helper (param : sort) (target : sort) :
    (sort * sort) list =
  let out =
    match (param, target) with
    | SortCall (f, xs), SortCall (g, ys)
      when f.value = g.value && List.length xs = List.length ys ->
        List.flatten (List.map2 get_bindings_helper xs ys)
    | SortCall (f, []), other -> [(SortCall (f, []), other)]
    | SeqSort a, SeqSort b -> get_bindings_helper a b
    | ArraySort (a1, b1), ArraySort (a2, b2) ->
        get_bindings_helper a1 a2 @ get_bindings_helper b1 b2
    | _ -> []
  in
  out

let get_bindings names with_params targets : environment =
  let flat =
    List.flatten
      (List.map2 (fun x y -> get_bindings_helper x y) with_params targets)
  in
  let flat = List.filter (fun (x, y) -> x <> y) flat in
  let candidates =
    List.map
      (fun x ->
        ( x
        , let cs =
            List.filter_map
              (fun (y, z) ->
                match y with
                | SortCall (v, []) when v.value = x.value -> Some z
                | _ -> None )
              flat
          in
          List.sort_uniq compare_sort cs ) )
      names
  in
  let pairs =
    List.map
      (fun (k, vs) ->
        match vs with
        | [x] -> (k.value, x)
        | [] -> (k.value, SortCall (k, []))
        | _ ->
            raise
              (TypeMismatch
                 (Printf.sprintf
                    "Cannot unify type parameter %s\nCandidate types are: %s"
                    (show_pstring k)
                    (String.concat ", " (List.map (fun a -> show_sort a) vs)) )
              ) )
      candidates
  in
  of_list pairs

let rec get_params (sorts : sort_def list) (datatypes : data_def list) :
    sort -> pstring list = function
  | IntSort | BoolSort | StringSort -> []
  | SeqSort a -> get_params sorts datatypes a
  | ArraySort (inp, out) ->
      (get_params sorts datatypes) inp @ (get_params sorts datatypes) out
  | SortCall (p, []) when is_data datatypes p || is_sort sorts p -> []
  | SortCall (p, []) -> [p]
  | SortCall (_, args) ->
      List.flatten (List.map (get_params sorts datatypes) args)

let unify_helper (sorts : sort_def list) (datatypes : data_def list)
    (templates : sort list) (data : sort list) (to_fill : sort) : sort =
  let params =
    List.flatten (List.map (get_params sorts datatypes) templates)
  in
  let env = get_bindings params templates data in
  eval_sort sorts datatypes env to_fill

let unify (sorts : sort_def list) (datatypes : data_def list)
    (left : sort list) (right : sort list) (to_fill : sort) : sort =
  let c1 = unify_helper sorts datatypes left right to_fill in
  let c2 = unify_helper sorts datatypes right left to_fill in
  if
    List.length (get_params sorts datatypes c1)
    <= List.length (get_params sorts datatypes c2)
  then c1
  else c2
