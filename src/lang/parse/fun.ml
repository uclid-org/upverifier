open Tokens
open P
open Common.Error
open Common
open Util
open Sort
open Term
open Printf

let parse_fun_defn_helper recursive sort_params toks =
  match toks with
  | (ID s, p) :: (LPAREN, _) :: toks ->
      let params, toks = parse_params toks in
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let body, toks =
        match toks with
        | (ASSIGN, _) :: toks ->
            let body, toks = parse_term false toks in
            (Some body, toks)
        | _ -> (None, toks)
      in
      ( { name= {value= s; position= p}
        ; recursive
        ; sort_params
        ; params
        ; body
        ; sort }
      , toks )
  | (ID s, p) :: toks ->
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      let body, toks =
        match toks with
        | (ASSIGN, _) :: toks ->
            let body, toks = parse_term false toks in
            (Some body, toks)
        | _ -> (None, toks)
      in
      ( { name= {value= s; position= p}
        ; recursive
        ; sort_params
        ; params= []
        ; body
        ; sort }
      , toks )
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_fun_defn_helper failed at %s %s"
              (show_token_name x) (show_pos p) ) )
  | _ -> raise (ParseError "parse_fun_defn_helper failed at end of input")

let parse_fun_defn toks =
  match toks with
  | (ID "recursive", _) :: (ID "function", _) :: (LBRACKET, _) :: toks ->
      let sort_params, toks = parse_names toks in
      parse_fun_defn_helper true sort_params toks
  | (ID "function", _) :: (LBRACKET, _) :: toks ->
      let sort_params, toks = parse_names toks in
      parse_fun_defn_helper false sort_params toks
  | (ID "recursive", _) :: (ID "function", _) :: toks ->
      parse_fun_defn_helper true [] toks
  | (ID "function", _) :: toks -> parse_fun_defn_helper false [] toks
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_fun_defn failed at %s %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_fun_defn failed at end of input")
