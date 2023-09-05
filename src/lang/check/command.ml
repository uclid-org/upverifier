open L3
open Common.Error
open Common
open Term
open Printf
open Sort

let rec typecheck_unary_primitive e arg_type datatypes =
  match (e, arg_type) with
  | Print _, SortCall (f, _) when is_data datatypes f -> true
  | Print _, SeqSort a -> typecheck_unary_primitive e a datatypes
  | Print _, ArraySort (a, b) ->
      typecheck_unary_primitive e a datatypes
      && typecheck_unary_primitive e b datatypes
  | Print _, IntSort | Print _, BoolSort | Print _, StringSort -> true
  | Assume _, BoolSort | Assert _, BoolSort -> true
  | _ -> false

let typecheck_command (interp : bool) (funs : fun_def list)
    (sorts : sort_def list) (datatypes : data_def list) (env : environment)
    (cmd : command) =
  let tc_term = typecheck_term funs sorts datatypes Symtab.empty env in
  match cmd with
  | Check -> ()
  | Push -> ()
  | Pop -> ()
  | Print (Right _) -> ()
  | Print (Left arg) as e ->
      let arg_t = tc_term arg in
      if not (typecheck_unary_primitive e arg_t datatypes) then
        raise
          (TypeMismatch
             (sprintf
                "Print command \"%s\" requires a printable type but got \"%s\""
                (show_command e) (show_sort arg_t) ) )
  | Assume arg as e ->
      let arg_t = tc_term arg in
      if not (typecheck_unary_primitive e arg_t datatypes) then
        raise
          (TypeMismatch
             (sprintf "Assume command \"%s\" requires \"%s\" but got \"%s\""
                (show_command e) (show_sort BoolSort) (show_sort arg_t) ) )
  | Assert arg as e ->
      let arg_t = tc_term arg in
      if not (typecheck_unary_primitive e arg_t datatypes) then
        raise
          (TypeMismatch
             (sprintf "Assert command \"%s\" requires \"%s\" but got \"%s\""
                (show_command e) (show_sort BoolSort) (show_sort arg_t) ) )
  | Choose ((_, sx), Some (_, sy), Some a, b) as e -> (
      let new_sx = eval_sort sorts datatypes env sx in
      let new_sy = eval_sort sorts datatypes env sy in
      let condSort = Option.map tc_term b in
      match tc_term a with
      | ArraySort (inp, out)
        when Option.is_some (matching_sort new_sx inp)
             && Option.is_some (matching_sort new_sy out)
             && (condSort = Some BoolSort || condSort = None) ->
          ()
      | _ ->
          raise
            (TypeMismatch
               (sprintf
                  "Choose command \"%s\" requires index and element sorts to match array. And condition must be boolean!"
                  (show_command e) ) ) )
  | Choose ((_, sx), None, None, b) as e -> (
      if not interp then ()
      else
        let condSort = Option.map tc_term b in
        match eval_sort sorts datatypes env sx with
        | SortCall (dt, _)
          when is_data datatypes dt
               && (condSort = Some BoolSort || condSort = None) ->
            ()
        | IntSort | BoolSort | StringSort -> ()
        | _ ->
            raise
              (TypeMismatch
                 (sprintf
                    "Choose command \"%s\" must be a datatype. And condition must be boolean!"
                    (show_command e) ) ) )
  | Choose _ as e ->
      raise
        (TypeMismatch
           (sprintf "Malformed Choose command \"%s\"!" (show_command e)) )
