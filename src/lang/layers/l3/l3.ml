include L2
open Printf
open Common

type program =
  { funs: fun_def list
  ; sorts: sort_def list
  ; datatypes: data_def list
  ; body: command list }

let show_sort_def (dfn : sort_def) : string =
  let params = String.concat ", " (List.map (fun x -> x.value) dfn.params) in
  sprintf "type [%s] %s := %s" params dfn.name.value (show_sort dfn.body)

let show_program (prog : program) : string =
  let tps =
    String.concat "\n" (List.map show_sort_def (List.rev prog.sorts))
  in
  let dts =
    String.concat "\n" (List.map show_data_def (List.rev prog.datatypes))
  in
  let fns =
    String.concat "\n" (List.map show_fun_def (List.rev prog.funs))
  in
  let cmds =
    String.concat "\n" (List.map show_command (List.rev prog.body))
  in
  sprintf "%s\n" (String.concat "\n\n" [tps; dts; fns; cmds])
