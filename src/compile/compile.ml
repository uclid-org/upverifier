open Smtlib
open Printf

let compile (prog : Smtlib.program) : string =
  let usorts =
    if List.length prog.datatypes > 0 then
      String.concat "\n"
        (List.map show_data_def
           (List.filter (fun dt -> List.length dt.cases = 0) prog.datatypes) )
    else ""
  in
  let dts =
    if List.length prog.datatypes > 0 then
      String.concat "\n"
        (List.map show_data_def
           (List.filter
              (fun dt -> List.length dt.cases > 0)
              (sort_datas prog.datatypes) ) )
    else ""
  in
  let chooses =
    String.concat "\n"
      (List.filter_map
         (fun c ->
           match c with
           | Choose ((x, s1), Some (y, s2), _, _) ->
               Some
                 (sprintf "(declare-const %s %s)\n(declare-const %s %s)"
                    x.value (show_sort s1) y.value (show_sort s2) )
           | Choose ((x, s1), None, _, _) ->
               Some (sprintf "(declare-const %s %s)" x.value (show_sort s1))
           | _ -> None )
         (List.rev prog.body) )
  in
  let ufns =
    String.concat "\n"
      (List.filter_map
         (fun (d : fun_def) ->
           match d.body with Some _ -> None | None -> Some (show_fun_def d)
           )
         (sort_funs prog.funs) )
  in
  let fns =
    String.concat "\n"
      (List.filter_map
         (fun (d : fun_def) ->
           match d.body with Some _ -> Some (show_fun_def d) | None -> None
           )
         (sort_funs prog.funs) )
  in
  let cmds = String.concat "" (List.map show_command (List.rev prog.body)) in
  let lines =
    List.filter_map
      (fun x -> if x = "" then None else Some x)
      [usorts; dts; chooses; ufns; fns; cmds]
  in
  sprintf "(set-logic ALL)\n\n%s\n" (String.concat "\n\n" lines)

let run_c filenames debug =
  let p = Parse.parse filenames in
  let l3 = Reduce.preprocess p debug in
  let _ = Check.check false l3 in
  let smtlib = Reduce.reduce l3 in
  compile smtlib
