open Tokens
open P
open Common.Error
open Common
open Sort
open Printf
open Util
open Term

let rec parse_fields toks =
  match toks with
  | (RBRACE, _) :: _ as toks -> ([], toks)
  | (ID "state", _) :: _ as toks -> ([], toks)
  | (VAR, _) :: toks ->
      let param, p, toks = get_id toks in
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_fields toks in
      (({value= param; position= p}, sort, false) :: rest, toks)
  | (GHOST, _) :: toks ->
      let param, p, toks = get_id toks in
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_fields toks in
      (({value= param; position= p}, sort, true) :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_fields failed at \"%s\" %s\nExpected \"state\", \"var\", or \"}\""
              (show_token_name x) (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_fields failed at end of input. Expected \"state\", \"var\", or \"}\""
        )

and parse_rest_fields toks =
  match toks with
  | (RBRACE, _) :: _ as toks -> ([], toks)
  | (ID "state", _) :: _ as toks -> ([], toks)
  | (VAR, _) :: toks ->
      let param, p, toks = get_id toks in
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_fields toks in
      (({value= param; position= p}, sort, false) :: rest, toks)
  | (GHOST, _) :: toks ->
      let param, p, toks = get_id toks in
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_fields toks in
      (({value= param; position= p}, sort, true) :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_rest_fields failed at %s. Expected \"state\", \"var\", or \"}\""
              (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_rest_fields failed at end of input. Expected \"state\", \"var\", or \"}\""
        )

let parse_handler_body on params toks =
  match toks with
  | (ID "do", _) :: (LBRACE, _) :: (RBRACE, _) :: toks ->
      ({on; params; body= None}, toks)
  | (ID "do", _) :: toks ->
      let toks = consume_token LBRACE toks in
      let body, toks = parse_term true toks in
      let toks = consume_token RBRACE toks in
      ({on; params; body= Some body}, toks)
  | (t, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_handler_body failed at \"%s\" %s\nExpected \"do\"!"
              (show_token_name t) (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_handler_body failed at end of input. Expected \"do\"!" )

let parse_handler_helper on toks =
  match toks with
  | (ID "do", _) :: _ as toks -> parse_handler_body on [] toks
  | (ID "with", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let params, toks = parse_params toks in
      parse_handler_body on params toks
  | (t, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_handler_helper failed at \"%s\" %s\nExpected \"do\" or \"with\"!"
              (show_token_name t) (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_handler_helper failed at end of input. Expected \"do\" or \"with\"!"
        )

let parse_handler toks =
  match toks with
  | (ID "on", _) :: (ID "entry", _) :: toks -> parse_handler_helper None toks
  | (ID "on", _) :: (ID event, epos) :: (do_or_with, dpos) :: toks
    when do_or_with = ID "do" || do_or_with = ID "with" ->
      parse_handler_helper
        (Some
           ( {value= event; position= epos}
           , {value= Common.gensym "UNDERSCORE"; position= epos} ) )
        ((do_or_with, dpos) :: toks)
  | (ID "on", _) :: (ID event, epos) :: (ID var, vpos) :: toks ->
      parse_handler_helper
        (Some ({value= event; position= epos}, {value= var; position= vpos}))
        toks
  | (t, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_handler failed at \"%s\" %s\nExpected \"on\"!"
              (show_token_name t) (show_pos p) ) )
  | _ ->
      raise
        (ParseError "parse_handler failed at end of input. Expected \"on\"!")

let rec parse_handlers toks =
  match toks with
  | (ID "on", _) :: (ID "entry", _) :: (ID "do", _) :: _ | (ID "on", _) :: _
    ->
      let handler, toks = parse_handler toks in
      let rest_handlers, toks = parse_handlers toks in
      (handler :: rest_handlers, toks)
  | _ -> ([], toks)

let rec parse_states toks =
  match toks with
  | (RBRACE, _) :: _ as toks -> ([], toks)
  | (ID "state", _) :: (ID name, p) :: toks ->
      let toks = consume_token LBRACE toks in
      let handlers, toks = parse_handlers toks in
      let handlers =
        (* If there is no entry handler, then add an empty one *)
        if List.for_all (fun h -> Option.is_some h.on) handlers then
          {on= None; params= []; body= None} :: handlers
        else handlers
      in
      let toks = consume_token RBRACE toks in
      let rest, toks = parse_rest_states toks in
      ({state_name= {value= name; position= p}; handlers} :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_states failed at \"%s\" %s\nExpected \"state\" or \"}\"!"
              (show_token_name x) (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_states failed at end of input. Expected \"state\" or \"}\"!"
        )

and parse_rest_states toks =
  match toks with
  | (RBRACE, _) :: _ as toks -> ([], toks)
  | (ID "state", _) :: (ID name, p) :: toks ->
      let toks = consume_token LBRACE toks in
      let handlers, toks = parse_handlers toks in
      let toks = consume_token RBRACE toks in
      let rest, toks = parse_rest_states toks in
      ({state_name= {value= name; position= p}; handlers} :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_rest_states failed at %s\nExpected \"state\" or \"}\"!"
              (show_pos p) ) )
  | _ ->
      raise
        (ParseError
           "parse_rest_states failed at end of input. Expected \"state\" or \"}\"!"
        )

let parse_machine_defn toks : machine_def * (token_name * pos) list =
  match toks with
  | (ID "machine", _) :: (ID s, pos) :: toks ->
      let toks = consume_token LBRACE toks in
      let fields, toks = parse_fields toks in
      let states, toks = parse_states toks in
      let toks = consume_token RBRACE toks in
      ({machine_name= {value= s; position= pos}; fields; states}, toks)
  | (ID "machine", _) :: (x, p) :: _ | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_machine_defn failed at \"%s\" %s"
              (show_token_name x) (show_pos p) ) )
  | _ -> raise (ParseError "parse_machine_defn failed at end of input")
