open Tokens
open P
open Common.Error
open Common
open Data
open Printf
open Util

let parse_event_defn toks : event_def * (token_name * pos) list =
  match toks with
  | (ID "event", pos) :: (ID s, p) :: toks ->
      let toks = consume_token ASSIGN toks in
      let toks = consume_token LBRACE toks in
      let sels, toks = parse_selectors toks in
      let case = ({value= s; position= p}, sels) in
      ({event_name= {value= s; position= pos}; payload= case}, toks)
  | (ID "event", _) :: (x, p) :: _ | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_event_defn failed at \"%s\" %s"
              (show_token_name x) (show_pos p) ) )
  | _ -> raise (ParseError "parse_event_defn failed at end of input")
