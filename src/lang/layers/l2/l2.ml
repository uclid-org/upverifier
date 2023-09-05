open Common
include L1
open Printf

type fun_def =
  { name: pstring
  ; recursive: bool
  ; sort_params: pstring list
  ; params: (pstring * sort) list
  ; body: expr option
  ; sort: sort }

let is_fun (defns : fun_def list) name =
  List.exists (fun (d : fun_def) -> d.name.value = name.value) defns

let get_fun (defns : fun_def list) name =
  List.find (fun (d : fun_def) -> d.name.value = name.value) defns

type program =
  {funs: fun_def list; datatypes: data_def list; body: command list}

let get_funs_from_commands cmds =
  List.flatten
    (List.map
       (fun c ->
         match c with
         | Choose ((x, sx), ys, _, _) ->
             let x_fun =
               { name= x
               ; recursive= false
               ; sort_params= []
               ; params= []
               ; body= None
               ; sort= sx }
             in
             x_fun
             ::
             ( match ys with
             | Some (y, sy) ->
                 [ { name= y
                   ; recursive= false
                   ; sort_params= []
                   ; params= []
                   ; body= None
                   ; sort= sy } ]
             | _ -> [] )
         | _ -> [] )
       cmds )

let show_fun_def (dfn : fun_def) : string =
  let sort_params =
    String.concat ", " (List.map (fun x -> x.value) dfn.sort_params)
  in
  let params = String.concat ", " (List.map show_selector dfn.params) in
  match dfn.body with
  | Some body ->
      let cmd = if dfn.recursive then "recursive function" else "function" in
      sprintf "%s [%s] %s (%s) : %s := \n\t%s" cmd sort_params dfn.name.value
        params (show_sort dfn.sort) (show_expr body)
  | None ->
      let cmd = "unknown function" in
      sprintf "%s [%s] %s (%s) : %s" cmd sort_params dfn.name.value params
        (show_sort dfn.sort)
