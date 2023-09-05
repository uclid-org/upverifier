(** Expand P syntax **)

open P
open Common
open Common.Error
open Printf

let first_machine_pos = ref none_pos

let last_machine_pos = ref none_pos

(* Parse.parse_string "type [t] set := Array[t, Bool]" *)
let std_lib_sorts =
  [ { name= mk_pstring "set" none_pos
    ; params= [mk_pstring "R" none_pos]
    ; body= ArraySort (SortCall (mk_pstring "R" none_pos, []), BoolSort) } ]

let combine_system (sysvars : field list) : L3.data_def =
  let param_pstring = mk_pstring "R" none_pos in
  let param_sort_call = SortCall (param_pstring, []) in
  let events_pstring = mk_pstring "events" none_pos in
  let machines_pstring = mk_pstring "machines" none_pos in
  let set_pstring = mk_pstring "set" none_pos in
  let machine = mk_pstring "machine" none_pos in
  let event_list = mk_pstring "event_list" none_pos in
  let machine_sort = SortCall (machine, []) in
  let event_list_sort = SortCall (event_list, [param_sort_call]) in
  let machines_sort = ArraySort (param_sort_call, machine_sort) in
  let events_sort = SortCall (set_pstring, [event_list_sort]) in
  let system = mk_pstring "system" (Common.just_after !last_machine_pos) in
  let cases =
    [ ( system
      , [(machines_pstring, machines_sort); (events_pstring, events_sort)]
        @ List.rev_map (fun (x, y, _) -> (x, y)) sysvars ) ]
  in
  {name= system; params= [param_pstring]; cases}

(** Take a list of events and combine them into a single datatype. For
    example,

    {[
      event eRequest := {request_id: Int}
      event eResponse := {response_id: Int, status: Bool}
    ]}

    Should reduce to

    {[
      data event :=
        | eRequest {request_id: Int}
        | eResponse {response_id: Int, status: Bool}
    ]} *)
let combine_events (events : event_def list) : L3.data_def =
  if List.length events = 0 then
    let name = mk_pstring "event" none_pos in
    let cases = [(mk_pstring "NONE_EVENT" none_pos, [])] in
    {name; params= []; cases}
  else
    let pos = (List.hd events).event_name.position in
    let name = {value= "event"; position= pos} in
    let cases = List.map (fun x -> x.payload) events in
    {name; params= []; cases}

(* data [R] event_list := | send {source: R, target: R, payload: event,
   history: event_list[R]} | empty *)
let generate_event_list (events : event_def list) : L3.data_def =
  let pos =
    if List.length events > 0 then
      Common.just_after (List.hd events).event_name.position
    else none_pos
  in
  let name = {value= "event_list"; position= pos} in
  let cases =
    [ ( mk_pstring "send" none_pos
      , [ ( mk_pstring "source" none_pos
          , SortCall (mk_pstring "R" none_pos, []) )
        ; ( mk_pstring "target" none_pos
          , SortCall (mk_pstring "R" none_pos, []) )
        ; ( mk_pstring "payload" none_pos
          , SortCall (mk_pstring "event" none_pos, []) )
        ; ( mk_pstring "history" none_pos
          , SortCall
              ( mk_pstring "event_list" none_pos
              , [SortCall (mk_pstring "R" none_pos, [])] ) ) ] )
    ; (mk_pstring "empty" none_pos, []) ]
  in
  {name; params= [mk_pstring "R" none_pos]; cases}

(** Take a list of machines and combine them into a single datatype. For
    example,

    {[
      machine Client
      {
        var client_id : Int
      }

      machine Server
      {
        var server_id : Int
      }
    ]}

    Should reduce to

    {[
      data machine :=
        | Client {client_id: Int}
        | Server {server_id: Int}
    ]} *)
let combine_machines (machines : machine_def list) : L3.data_def =
  if List.length machines = 0 then
    let name = mk_pstring "machine" none_pos in
    let cases = [(mk_pstring "NONE_MACHINE" none_pos, [])] in
    {name; params= []; cases}
  else
    let pos = (List.hd machines).machine_name.position in
    let name = {value= "machine"; position= pos} in
    let cases =
      List.map
        (fun (m : machine_def) ->
          let s = m.machine_name.value in
          let p = m.machine_name.position in
          let fields = List.map (fun (x, y, _) -> (x, y)) m.fields in
          if List.length m.states > 0 then
            let state_sort =
              SortCall ({value= s ^ "_state"; position= p}, [])
            in
            let state_field =
              ( { value= s ^ "_state"
                ; position= (List.hd m.states).state_name.position }
              , state_sort )
            in
            let entry_field =
              ( {value= s ^ "_entry"; position= m.machine_name.position}
              , BoolSort )
            in
            (m.machine_name, state_field :: entry_field :: fields)
          else (m.machine_name, fields) )
        machines
    in
    {name; params= []; cases}

(** Take a machines and create an enum for its states. For example,

    {[
      machine Client
      {
          var client_id : Int
          var x : Bool

          state first {

          }

          state second {

          }
      }
    ]}

    Should produce

    {[ data Client_state := first | second ]} *)
let combine_states (machine : machine_def) : L3.data_def option =
  if List.length machine.states = 0 then None
  else
    let pos = machine.machine_name.position in
    let name =
      {value= machine.machine_name.value ^ "_state"; position= pos}
    in
    let cases = List.map (fun x -> (x.state_name, [])) machine.states in
    Some {name; params= []; cases}

let rec reduce_no_p (inp : expr) : L1.expr =
  let red = reduce_no_p in
  match inp with
  | True -> True
  | False -> False
  | Num v -> Num v
  | Str v -> Str v
  | Let (var, exp, body) -> Let (var, red exp, red body)
  | If (test_exp, then_exp, Some else_exp) ->
      If (red test_exp, red then_exp, red else_exp)
  | If (_, _, None) as e ->
      raise
        (PSyntaxError
           (sprintf "Unexpected If without Else! %s" (show_expr e)) )
  | Call (f, args) -> Call (f, List.map red args)
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
  | Const (e, t) -> Const (red e, t)
  | As (e, t) -> As (red e, t)
  | Forall (ps, b) -> Forall (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Exists (ps, b) -> Exists (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Do [] -> raise (PSyntaxError "Empty DO!")
  | Do [left] -> red left
  | Do (left :: right) -> Do [red left; red (Do right)]
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Assign (lhs, rhs) -> Assign (red lhs, red rhs)
  | Send (_, _) as e ->
      raise (PSyntaxError (sprintf "Unexpected Send! %s" (show_expr e)))
  | Goto s ->
      raise (PSyntaxError (sprintf "Unexpected Goto! %s" (show_pstring s)))
  | Apply (count, f, args) ->
      let new_args = List.map red args in
      List.fold_left
        (fun acc _ -> L1.Call (f, acc :: List.tl new_args))
        (List.hd new_args)
        (List.init count (fun x -> x + 1))

let rec reduce_var_and_goto (fields : string list) (machine_name : pstring)
    (machine : expr) (inp : expr) : expr =
  let red = reduce_var_and_goto fields machine_name machine in
  match inp with
  | True -> True
  | False -> False
  | Num v -> Num v
  | Str v -> Str v
  | Call (v, []) when List.mem v.value fields -> Project (v, red machine)
  | Let (var, exp, body) -> Let (var, red exp, red body)
  | If (test_exp, then_exp, else_exp) ->
      If (red test_exp, red then_exp, Option.map red else_exp)
  | Call (f, args) -> Call (f, List.map red args)
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
  | Const (e, t) -> Const (red e, t)
  | As (e, t) -> As (red e, t)
  | Forall (ps, b) -> Forall (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Exists (ps, b) -> Exists (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Do [] -> raise (PSyntaxError "Empty DO!")
  | Do [left] -> red left
  | Do (left :: right) -> (
    match red left with
    | Do (l :: r) ->
        Do [l; Do (r @ [red (Do right)])]
        (* We introdue a do on gotos so we have to deal with it here *)
    | new_left -> Do [new_left; red (Do right)] )
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Assign (lhs, rhs) -> Assign (red lhs, red rhs)
  | Send (target, payload) -> Send (red target, red payload)
  | Goto s ->
      let state_selector =
        {value= machine_name.value ^ "_state"; position= s.position}
      in
      let state_var = Project (state_selector, machine) in
      let entry_selector =
        {value= machine_name.value ^ "_entry"; position= s.position}
      in
      let entry_var = Project (entry_selector, machine) in
      Do [Assign (state_var, Call (s, [])); Assign (entry_var, True)]
  | Apply (count, f, args) -> Apply (count, f, List.map red args)

let rec reduce_sends (system : pstring * expr) (source : expr)
    (history : expr option) (inp : expr) : L1.expr =
  let red = reduce_sends system source history in
  match inp with
  | True -> True
  | False -> False
  | Num v -> Num v
  | Str v -> Str v
  | Let (var, exp, body) -> Let (var, red exp, red body)
  | If (test_exp, then_exp, Some else_exp) ->
      If (red test_exp, red then_exp, red else_exp)
  | If (test_exp, then_exp, None) ->
      If
        ( red test_exp
        , red then_exp
        , Let (fst system, red (snd system), Call (fst system, [])) )
  | Call (f, args) -> Call (f, List.map red args)
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
  | Const (e, t) -> Const (red e, t)
  | As (e, t) -> As (red e, t)
  | Forall (ps, b) -> Forall (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Exists (ps, b) -> Exists (List.map (fun (x, y) -> (x, y)) ps, red b)
  | Do [] -> raise (PSyntaxError "Empty DO!")
  | Do [left] -> red left
  | Do (left :: right) -> Do [red left; red (Do right)]
  | Update (a, b, c) -> Update (red a, red b, red c)
  | Assign (lhs, rhs) -> Assign (red lhs, red rhs)
  | Send (target, payload) ->
      let cons = mk_pstring "send" none_pos in
      let nil = mk_pstring "empty" none_pos in
      let parametric = SortCall (mk_pstring "R" none_pos, []) in
      let event_list =
        SortCall (mk_pstring "event_list" none_pos, [parametric])
      in
      let tail =
        match history with
        | Some h -> h
        | None -> As (Call (nil, []), event_list)
      in
      let el = Call (cons, [source; target; payload; tail]) in
      let events_sel = mk_pstring "events" none_pos in
      let events = Project (events_sel, snd system) in
      let lhs = Select (events, el) in
      Assign (red lhs, True)
  | Goto s ->
      raise (PSyntaxError (sprintf "Unexpected Goto! %s" (show_pstring s)))
  | Apply (_, f, _) ->
      raise (PSyntaxError (sprintf "Unexpected Apply! %s" (show_pstring f)))

let reduce_handler_expr fields machine_name system machine source history e =
  reduce_var_and_goto fields machine_name machine e
  |> reduce_sends system source history

let process_handler_body (machine_name : pstring) (fields : string list)
    (state : expr) (entry : expr) (system : pstring * expr)
    (reference : expr) (history : (expr * pstring) option) (body : expr) :
    L1.expr =
  let machine_pos = machine_name.position in
  let machines_selector = mk_pstring "machines" machine_pos in
  let state_selector =
    {value= machine_name.value ^ "_state"; position= machine_name.position}
  in
  let entry_selector =
    {value= machine_name.value ^ "_entry"; position= machine_name.position}
  in
  let m = Select (Project (machines_selector, snd system), reference) in
  let m_state = Project (state_selector, m) in
  let m_entry = Project (entry_selector, m) in
  match history with
  | Some (e, k) ->
      let payload_selector =
        {value= "payload"; position= machine_name.position}
      in
      let sevents = Project (mk_pstring "events" k.position, snd system) in
      let selected_event = Select (sevents, e) in
      let payload = Project (payload_selector, e) in
      reduce_handler_expr fields machine_name system m reference (Some e)
        (If
           ( And
               ( Is (payload, k)
               , And
                   ( selected_event
                   , And (Eq (m_state, state), Eq (m_entry, entry)) ) )
           , body
           , Some (snd system) ) )
  | None ->
      reduce_handler_expr fields machine_name system m reference None
        (If
           ( And (Eq (m_state, state), Eq (m_entry, entry))
           , body
           , Some (snd system) ) )

let process_handler (machine_name : pstring) (state_name : pstring)
    (fields : string list) (state : expr) (h : handler_def) : L3.fun_def =
  let machine_pos = machine_name.position in
  let ref_sort_name = mk_pstring "R" machine_pos in
  let sort_param_names = [ref_sort_name] in
  let sort_param_sorts =
    List.map (fun x -> SortCall (x, [])) sort_param_names
  in
  let event_sort_name = mk_pstring "event_list" machine_pos in
  let system_sort_name = mk_pstring "system" machine_pos in
  let system_param_name = mk_pstring "s" machine_pos in
  let system_sort = SortCall (system_sort_name, sort_param_sorts) in
  let system = Call (system_param_name, []) in
  let reference_name = mk_pstring "this" machine_pos in
  let reference_sort = SortCall (ref_sort_name, []) in
  let reference = Call (reference_name, []) in
  let new_params =
    [(system_param_name, system_sort); (reference_name, reference_sort)]
  in
  let entry = if Option.is_none h.on then True else False in
  let event_arg =
    match h.on with
    | Some (_, v) -> [(v, SortCall (event_sort_name, sort_param_sorts))]
    | None -> []
  in
  let new_body =
    if Option.is_some h.body then Option.get h.body else system
  in
  let fields =
    match List.find_opt (fun (x, _) -> List.mem x.value fields) h.params with
    | Some (x, _) ->
        raise
          (PSyntaxError
             (sprintf
                "Handler parameter cannot have same name as a field! %s"
                (show_pstring x) ) )
    | None -> fields
  in
  let new_body =
    match h.on with
    | Some (k, _) ->
        let ev = Call (fst (List.hd event_arg), []) in
        let sevents = Project (mk_pstring "events" k.position, system) in
        let selected_event = Select (sevents, ev) in
        let remove_event = Assign (selected_event, False) in
        process_handler_body machine_name fields state entry
          (system_param_name, system)
          reference
          (Some (ev, k))
          (Do [remove_event; new_body])
    | None ->
        process_handler_body machine_name fields state entry
          (system_param_name, system)
          reference None
          (Do
             [ Assign
                 ( Call
                     (mk_pstring (machine_name.value ^ "_entry") none_pos, [])
                 , False )
             ; new_body ] )
  in
  let handler_name =
    match h.on with
    | Some (e, _) ->
        { value= (machine_name.value ^ "_" ^ state_name.value) ^ "_" ^ e.value
        ; position= e.position }
    | None ->
        { value= machine_name.value ^ "_" ^ state_name.value ^ "_entry"
        ; position= state_name.position }
  in
  { name= handler_name
  ; recursive= false
  ; sort_params= sort_param_names
  ; params= new_params @ event_arg @ h.params
  ; body= Some new_body
  ; sort= system_sort }

let process_state_handlers (machine_name : pstring) (fields : string list)
    (state : state_def) : L3.fun_def list =
  let state_expr = Call (state.state_name, []) in
  List.map
    (process_handler machine_name state.state_name fields state_expr)
    state.handlers

let process_machine_handlers (machine : machine_def) : L3.fun_def list =
  let fields =
    List.map
      (fun x -> x.value)
      (List.map (fun (x, _, _) -> x) machine.fields)
    @ [ machine.machine_name.value ^ "_state"
      ; machine.machine_name.value ^ "_entry" ]
  in
  List.flatten
    (List.map
       (process_state_handlers machine.machine_name fields)
       machine.states )

let reduce_command_fuzzed : command -> L3.command option = function
  | Check -> Some Check
  | Push -> Some Push
  | Pop -> Some Pop
  | Print (Left e) -> Some (Print (Left (reduce_no_p e)))
  | Print (Right e) -> Some (Print (Right e))
  | Assume e -> Some (Assume (reduce_no_p e))
  | Assert e -> Some (Assert (reduce_no_p e))
  | Choose (xs, ys, a, b) ->
      Some
        (Choose (xs, ys, Option.map reduce_no_p a, Option.map reduce_no_p b))
  | Induction _ | Fuzzed _ -> None

let reduce_command_no_p : command -> L3.command = function
  | Check -> Check
  | Push -> Push
  | Pop -> Pop
  | Print (Left e) -> Print (Left (reduce_no_p e))
  | Print (Right e) -> Print (Right e)
  | Assume e -> Assume (reduce_no_p e)
  | Assert e -> Assert (reduce_no_p e)
  | Choose (xs, ys, a, b) ->
      Choose (xs, ys, Option.map reduce_no_p a, Option.map reduce_no_p b)
  | Fuzzed ((n, _), _, _) ->
      raise
        (PSyntaxError
           (sprintf "Unexpected fuzzed command! %s" (show_pstring n)) )
  | Induction ((n, _), _, _) ->
      raise
        (PSyntaxError
           (sprintf "Unexpected induction command! %s" (show_pstring n)) )

let reduce_fun (defn0 : fun_def) : L3.fun_def =
  let new_params = List.map (fun (n, s) -> (n, s)) defn0.params in
  let new_sort = defn0.sort in
  let new_body = Option.map reduce_no_p defn0.body in
  { name= defn0.name
  ; recursive= defn0.recursive
  ; sort_params= defn0.sort_params
  ; params= new_params
  ; body= new_body
  ; sort= new_sort }

let generate_next (machines : machine_def list) (events : event_def list)
    (handlers : L2.fun_def list) : L2.fun_def =
  let after_last_handler =
    if List.length handlers > 0 then
      let last_handler_pos = (List.hd handlers).name.position in
      {line= last_handler_pos.line + 1; column= 0; file= None}
    else none_pos
  in
  let inner_params =
    List.flatten
      (List.map
         (fun (m : machine_def) ->
           List.flatten
             (List.map
                (fun (s : state_def) ->
                  List.flatten
                    (List.map
                       (fun (h : handler_def) -> h.params)
                       s.handlers ) )
                m.states ) )
         (List.rev machines) )
  in
  let ref_sort_name = mk_pstring "R" after_last_handler in
  let ref_sort = SortCall (ref_sort_name, []) in
  let system_sort_name = mk_pstring "system" after_last_handler in
  let system_sort = SortCall (system_sort_name, [ref_sort]) in
  let event_list_name = mk_pstring "event_list" after_last_handler in
  let event_list_sort = SortCall (event_list_name, [ref_sort]) in
  let ref_name = mk_pstring "this" after_last_handler in
  let system_name = mk_pstring "s" after_last_handler in
  let event_name = mk_pstring "e" after_last_handler in
  let choice_name = mk_pstring "c" after_last_handler in
  let ref_param = L3.Call (ref_name, []) in
  let system_param = L3.Call (system_name, []) in
  let event_param = L3.Call (event_name, []) in
  let choice_param = L3.Call (choice_name, []) in
  let smachines =
    L3.Project (mk_pstring "machines" after_last_handler, system_param)
  in
  let payload =
    L3.Project (mk_pstring "payload" after_last_handler, event_param)
  in
  let target =
    L3.Project (mk_pstring "target" after_last_handler, event_param)
  in
  let next_entry =
    let m = L3.Select (smachines, ref_param) in
    List.fold_left
      (fun (acc1 : L3.expr) mdef ->
        let sel_name =
          mk_pstring (mdef.machine_name.value ^ "_state") after_last_handler
        in
        let m_state = L3.Project (sel_name, m) in
        let cond = L3.Is (m, mdef.machine_name) in
        L3.If
          ( cond
          , List.fold_left
              (fun acc2 state ->
                let cond = L3.Is (m_state, state.state_name) in
                let call_name =
                  mk_pstring
                    ( mdef.machine_name.value ^ "_" ^ state.state_name.value
                    ^ "_entry" )
                    after_last_handler
                in
                if L2.is_fun handlers call_name then
                  let the_call =
                    L3.Call
                      ( call_name
                      , [system_param; ref_param]
                        @ List.map
                            (fun (x, _) -> L1.Call (x, []))
                            (List.tl
                               (List.tl
                                  (L2.get_fun handlers call_name).params ) )
                      )
                  in
                  L3.If (cond, the_call, acc2)
                else acc2 )
              system_param mdef.states
          , acc1 ) )
      system_param machines
  in
  let next_event =
    let m = L3.Select (smachines, target) in
    List.fold_left
      (fun (acc1 : L3.expr) mdef ->
        let sel_name =
          mk_pstring (mdef.machine_name.value ^ "_state") after_last_handler
        in
        let m_state = L3.Project (sel_name, m) in
        let cond = L3.Is (m, mdef.machine_name) in
        L3.If
          ( cond
          , List.fold_left
              (fun acc2 state ->
                let cond = L3.Is (m_state, state.state_name) in
                L3.If
                  ( cond
                  , List.fold_left
                      (fun (acc3 : L3.expr) ev ->
                        let cond = L3.Is (payload, ev.event_name) in
                        let call_name =
                          mk_pstring
                            ( mdef.machine_name.value ^ "_"
                            ^ state.state_name.value ^ "_"
                            ^ ev.event_name.value )
                            after_last_handler
                        in
                        if L2.is_fun handlers call_name then
                          let the_call =
                            L3.Call
                              ( call_name
                              , [system_param; target; event_param]
                                @ List.map
                                    (fun (x, _) -> L1.Call (x, []))
                                    (List.tl
                                       (List.tl
                                          (List.tl
                                             (L2.get_fun handlers call_name)
                                               .params ) ) ) )
                          in
                          L3.If (cond, the_call, acc3)
                        else acc3 )
                      system_param events
                  , acc2 ) )
              system_param mdef.states
          , acc1 ) )
      system_param machines
  in
  let next_event =
    L3.If
      ( L3.Is (event_param, mk_pstring "empty" after_last_handler)
      , system_param
      , next_event )
  in
  let next_body : L3.expr = If (choice_param, next_entry, next_event) in
  { name= mk_pstring "next" after_last_handler
  ; recursive= false
  ; sort_params= [ref_sort_name]
  ; params=
      [ (system_name, system_sort)
      ; (ref_name, ref_sort)
      ; (event_name, event_list_sort)
      ; (choice_name, BoolSort) ]
      @ inner_params
  ; body= Some next_body
  ; sort= system_sort }

let split list n =
  let rec aux i acc = function
    | [] -> (List.rev acc, [])
    | h :: t as l ->
        if i = 0 then (List.rev acc, l) else aux (i - 1) (h :: acc) t
  in
  aux n [] list

let expand_symbolic (name : pstring) (sort : sort) (start : expr)
    (nextf : L3.fun_def) (steps : int) : fun_def list * command list =
  let choices = ref [] in
  let universe =
    match sort with
    | SortCall (s, [u]) when s.value = "system" -> u
    | s ->
        raise
          (PSyntaxError
             (sprintf
                "Unexpected sort to fuzz. Got %s but needed system[R] for %s"
                (show_sort s) (show_pstring name) ) )
  in
  let once previous pos =
    let mref =
      let mname = mk_fresh_pstring "m" (Common.just_after pos) in
      choices := Choose ((mname, universe), None, None, None) :: !choices ;
      Call (mname, [])
    in
    let event =
      let ename = mk_fresh_pstring "e" (Common.just_after pos) in
      let yname = mk_fresh_pstring "y" (Common.just_after pos) in
      let etype =
        SortCall (mk_pstring "event_list" name.position, [universe])
      in
      let events = Project (mk_pstring "events" name.position, previous) in
      choices :=
        Choose ((ename, etype), Some (yname, BoolSort), Some events, None)
        :: !choices ;
      Call (ename, [])
    in
    let choice =
      let cname = mk_fresh_pstring "c" (Common.just_after pos) in
      choices := Choose ((cname, BoolSort), None, None, None) :: !choices ;
      Call (cname, [])
    in
    let new_args =
      List.map
        (fun (x, s) ->
          let new_name = mk_fresh_pstring x.value (Common.just_after pos) in
          choices := Choose ((new_name, s), None, None, None) :: !choices ;
          Call (new_name, []) )
        (snd (split nextf.params 4))
    in
    Call
      ( {value= nextf.name.value; position= name.position}
      , [previous; mref; event; choice] @ new_args )
  in
  let start_f =
    { name= mk_fresh_pstring (name.value ^ "B") (just_after name.position)
    ; recursive= false
    ; sort_params= []
    ; params= []
    ; body= Some start
    ; sort }
  in
  let new_funs =
    List.fold_left
      (fun acc i ->
        let called = Call ((List.hd acc).name, []) in
        let body = once called (List.hd acc).name.position in
        { name=
            ( if i = steps then
              mk_pstring name.value (Common.line_after name.position)
            else
              (mk_fresh_pstring (name.value ^ "C"))
                (Common.just_after (List.hd acc).name.position) )
        ; recursive= false
        ; sort_params= []
        ; params= []
        ; body= Some body
        ; sort }
        :: acc )
      [start_f]
      (List.init steps (fun x -> x + 1))
  in
  (new_funs, !choices)

let expand_fuzzed (name : pstring) (sort : sort) (start : expr)
    (nextf : L3.fun_def) (steps : int) : fun_def list * command list =
  let funs, choices = expand_symbolic name sort start nextf steps in
  (funs, choices)

let expand_induction (name : pstring) (sort : sort) (nextf : L3.fun_def)
    (steps : int) (invariants : (pstring * expr) list) :
    fun_def list * command list =
  let curr = Call (name, []) in
  let invariant_funs =
    List.map
      (fun i ->
        { name= fst i
        ; recursive= false
        ; sort_params= []
        ; params= [(name, sort)]
        ; body= Some (snd i)
        ; sort= BoolSort } )
      invariants
  in
  let assertions =
    List.flatten
      (List.map
         (fun i ->
           [ Pop
           ; Check
           ; Print (Right ("- " ^ i.name.value))
           ; Assert (Call (i.name, [curr]))
           ; Push ] )
         invariant_funs )
  in
  let before =
    { name=
        mk_fresh_pstring (name.value ^ "A")
          (Common.just_before name.position)
    ; recursive= false
    ; sort_params= []
    ; params= []
    ; body= None
    ; sort }
  in
  let start = Call (before.name, []) in
  let new_funs, new_commands = expand_symbolic name sort start nextf steps in
  let new_fun_calls = List.map (fun f -> Call (f.name, [])) new_funs in
  let assumptions =
    List.flatten
      (List.map
         (fun f ->
           List.map (fun i -> Assume (Call (i.name, [f]))) invariant_funs )
         (List.tl new_fun_calls) )
  in
  ( new_funs @ (before :: invariant_funs)
  , assertions
    @ Print (Right "Invariants Hold (Want UNSAT):")
      ::
      ( if !Common.check_feasible then
        [Check; Print (Right "Assumptions Feasible (Want SAT):")]
      else [] )
    @ assumptions @ new_commands )

let rec check_expr (ghosts : pstring list) (allowed : bool) (body : expr) :
    unit =
  let red = check_expr ghosts allowed in
  match body with
  | True | False | Num _ | Goto _ | Str _ -> ()
  | Let (p, exp, body) ->
      check_expr (List.filter (fun x -> x.value = p.value) ghosts) false exp ;
      red body
  | If (test_exp, then_exp, else_exp) ->
      let _ = Option.map red else_exp in
      red test_exp ; red then_exp
  | Call (p, _)
    when List.exists (fun x -> x.value = p.value) ghosts && not allowed ->
      raise
        (PSyntaxError
           (sprintf "Ghost variable only allowed on left-hand-sides! %s"
              (show_pstring p) ) )
  | Call (_, args) -> List.iter red args
  | Project (_, arg) -> red arg
  | Select (_, arg) -> red arg
  | Not arg -> red arg
  | And (arg1, arg2) -> red arg1 ; red arg2
  | Or (arg1, arg2) -> red arg1 ; red arg2
  | Implies (arg1, arg2) -> red arg1 ; red arg2
  | Plus (arg1, arg2) -> red arg1 ; red arg2
  | Minus (arg1, arg2) -> red arg1 ; red arg2
  | Times (arg1, arg2) -> red arg1 ; red arg2
  | Concat (arg1, arg2) -> red arg1 ; red arg2
  | Eq (arg1, arg2) -> red arg1 ; red arg2
  | Is (arg1, _) -> red arg1
  | Prefix (arg1, arg2) -> red arg1 ; red arg2
  | Suffix (arg1, arg2) -> red arg1 ; red arg2
  | Contains (arg1, arg2) -> red arg1 ; red arg2
  | Lt (arg1, arg2) -> red arg1 ; red arg2
  | Lte (arg1, arg2) -> red arg1 ; red arg2
  | Gt (arg1, arg2) -> red arg1 ; red arg2
  | Gte (arg1, arg2) -> red arg1 ; red arg2
  | Length e -> red e
  | Unit e -> red e
  | Const (e, _) -> red e
  | As (e, _) -> red e
  | Forall (_, b) -> red b
  | Exists (_, b) -> red b
  | Do [] -> raise (PSyntaxError "Empty DO!")
  | Do [left] -> red left
  | Do (left :: right) -> red left ; red (Do right)
  | Update (a, b, c) -> red a ; red b ; red c
  | Assign (lhs, rhs) ->
      red lhs ;
      check_expr ghosts false rhs
  | Apply (_, _, args) -> List.iter red args
  | Send (target, payload) ->
      check_expr ghosts false target ;
      check_expr ghosts false payload

let check_handler (ghosts : pstring list) (h : handler_def) : unit =
  let _ = Option.map (check_expr ghosts true) h.body in
  ()

let check_machine (m : P.machine_def) : unit =
  let ghosts =
    List.filter_map (fun (f, _, g) -> if g then Some f else None) m.fields
  in
  List.iter (check_handler ghosts)
    (List.flatten (List.map (fun s -> s.handlers) m.states))

let check_p (prog : P.program) : unit =
  if
    List.length
      (List.filter
         (fun c -> match c with Induction _ -> true | _ -> false)
         prog.body )
    > 1
  then raise (PSyntaxError "Maximum of one induction proof at a time!") ;
  List.iter check_machine prog.machines

let reduce (prog : P.program) : L3.program =
  let _ = check_p prog in
  let reduced_funs = List.map reduce_fun prog.funs in
  if List.length prog.machines = 0 && List.length prog.events = 0 then
    let reduced_commands = List.map reduce_command_no_p prog.body in
    { funs= reduced_funs
    ; sorts= prog.sorts
    ; datatypes= prog.datatypes
    ; body= reduced_commands }
  else
    let _ =
      if List.length prog.machines = 0 then (
        first_machine_pos := none_pos ;
        last_machine_pos := none_pos )
      else (
        first_machine_pos :=
          (List.hd (List.rev prog.machines)).machine_name.position ;
        last_machine_pos := (List.hd prog.machines).machine_name.position )
    in
    let states = List.filter_map combine_states prog.machines in
    let event_machine_system =
      [ combine_events prog.events
      ; combine_machines prog.machines
      ; combine_system prog.sysvars
      ; generate_event_list prog.events ]
    in
    let new_datatypes = prog.datatypes @ states @ event_machine_system in
    let handlers =
      List.flatten (List.map process_machine_handlers prog.machines)
    in
    (* Sort so that we can put the next after the last *)
    let handlers =
      List.sort
        (fun (f : L2.fun_def) g ->
          let compare_fst =
            compare g.name.position.line f.name.position.line
          in
          if compare_fst <> 0 then compare_fst
          else compare g.name.position.column f.name.position.column )
        handlers
    in
    let next_fun = generate_next prog.machines prog.events handlers in
    let new_funs, new_commands =
      List.map
        (fun c ->
          match c with
          | Fuzzed ((name, sort), start, steps) ->
              expand_fuzzed name sort start next_fun steps
          | Induction ((name, sort), steps, invariants) ->
              expand_induction name sort next_fun steps invariants
          | c -> ([], [c]) )
        prog.body
      |> List.fold_left
           (fun (acc1, acc2) (x1, x2) -> (acc1 @ x1, acc2 @ x2))
           ([], [])
    in
    let new_funs = List.map reduce_fun new_funs in
    let new_commands = List.filter_map reduce_command_fuzzed new_commands in
    let new_funs = (next_fun :: handlers) @ new_funs @ reduced_funs in
    { funs= new_funs
    ; sorts= prog.sorts @ std_lib_sorts
    ; datatypes= new_datatypes
    ; body= new_commands }
