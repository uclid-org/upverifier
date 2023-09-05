open Smtlib
open Common
open Common.Error
open Value
open Term
open Util

let interp_command (funs : fun_def list) (datatypes : data_def list)
    (env : environment) : command -> environment = function
  | Print (Left expr) ->
      let v = interp_term funs datatypes env expr in
      display_value v
      |> fun x ->
      Printf.sprintf "%s\n" x |> output_string !output_channel ;
      env
  | Print (Right s) ->
      Printf.sprintf "%s\n" s |> output_string !output_channel ;
      env
  | Assert expr | Assume expr -> (
    match interp_term funs datatypes env expr with
    | Bool _ when Symtab.mem "CHECKSTATUS" env ->
        let update =
          interp_term funs datatypes env
            (And (expr, Call (mk_pstring "CHECKSTATUS" none_pos, [])))
        in
        Symtab.add "CHECKSTATUS" update env
    | Bool _ as v -> Symtab.add "CHECKSTATUS" v env
    | _ ->
        raise (Stuck (Printf.sprintf "Failed assert: %s\n" (show_expr expr)))
    )
  | Check when Symtab.mem "CHECKSTATUS" env ->
      let result = Symtab.find "CHECKSTATUS" env in
      Printf.sprintf "CHECK: %s\n" (display_value result)
      |> output_string !output_channel ;
      env
  | Check -> env
  | Choose ((x, _), Some (y, _), Some a, b) -> (
      let interp = interp_term funs datatypes in
      match interp env a with
      | Array (pairs, _, _) -> (
        match
          List.find_opt
            (fun (left, right) ->
              let fvar_env =
                env |> Symtab.add x.value left |> Symtab.add y.value right
              in
              let b_check = Option.map (interp fvar_env) b in
              b_check = Some (Bool true) || b_check = None )
            pairs
        with
        | Some (left, right) ->
            env |> Symtab.add x.value left |> Symtab.add y.value right
        | None when Option.is_some b ->
            raise
              (Stuck
                 (Printf.sprintf
                    "Failed to find a pair (%s, %s) in \"%s\" that satisfies \"%s\"! %s"
                    x.value y.value (show_expr a)
                    (show_expr (Option.get b))
                    (show_pos x.position) ) )
        | None ->
            raise
              (Stuck
                 (Printf.sprintf
                    "Failed to find a pair (%s, %s) in \"%s\"! %s" x.value
                    y.value (show_expr a) (show_pos x.position) ) ) )
      | _ -> raise (Stuck "Choose must be from an array!") )
  | Choose ((x, s), None, None, b) -> (
      let interp = interp_term funs datatypes in
      let instances = get_instances_of_sort 10 datatypes s in
      match
        List.find_opt
          (fun i ->
            let fvar_env = env |> Symtab.add x.value (interp env i) in
            let b_check = Option.map (interp fvar_env) b in
            b_check = Some (Bool true) || b_check = None )
          instances
      with
      | Some i -> env |> Symtab.add x.value (interp env i)
      | None when Option.is_some b ->
          raise
            (Stuck
               (Printf.sprintf
                  "Failed to find a %s that satisfies \"%s\"! %s" x.value
                  (show_expr (Option.get b))
                  (show_pos x.position) ) )
      | None ->
          raise
            (Stuck
               (Printf.sprintf "Failed to find a %s %s" x.value
                  (show_pos x.position) ) ) )
  | Choose _ -> raise (Stuck "Malformed Choose!")
  | Push | Pop -> env
