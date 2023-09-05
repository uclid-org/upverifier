open Tokens
open P
open Common.Error
open Common
open Sort
open Printf

let rec parse_selectors toks =
  match toks with
  | (RBRACE, _) :: toks -> ([], toks)
  | (ID param, p) :: (COLON, _) :: toks ->
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_selectors toks in
      (({value= param; position= p}, sort) :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_selectors failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_selectors failed at end of input")

and parse_rest_selectors toks =
  match toks with
  | (RBRACE, _) :: toks -> ([], toks)
  | (COMMA, _) :: (ID param, p) :: (COLON, _) :: toks ->
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_selectors toks in
      (({value= param; position= p}, sort) :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_rest_selectors failed at %s" (show_pos p)) )
  | _ -> raise (ParseError "parse_rest_selectors failed at end of input")

let rec parse_cases toks =
  match toks with
  | (BAR, _) :: (ID cons, p) :: (LBRACE, _) :: toks
   |(ID cons, p) :: (LBRACE, _) :: toks ->
      let selectors, toks = parse_selectors toks in
      let rest, toks = parse_rest_cases toks in
      (({value= cons; position= p}, selectors) :: rest, toks)
  | (BAR, _) :: (ID cons, p) :: toks | (ID cons, p) :: toks ->
      let rest, toks = parse_rest_cases toks in
      (({value= cons; position= p}, []) :: rest, toks)
  | _ -> ([], toks)

and parse_rest_cases toks =
  match toks with
  | (BAR, _) :: (ID cons, p) :: (LBRACE, _) :: toks ->
      let selectors, toks = parse_selectors toks in
      let rest, toks = parse_rest_cases toks in
      (({value= cons; position= p}, selectors) :: rest, toks)
  | (BAR, _) :: (ID cons, p) :: toks ->
      let rest, toks = parse_rest_cases toks in
      (({value= cons; position= p}, []) :: rest, toks)
  | _ -> ([], toks)

let parse_data_defn toks =
  match toks with
  | (DATA, _) :: (LBRACKET, pos) :: toks ->
      let params, toks = parse_names toks in
      let s, p, toks =
        match toks with
        | (ID s, p) :: toks -> (s, p, toks)
        | _ ->
            raise
              (ParseError
                 (sprintf "parse_data_defn failed at \"%s\" %s"
                    (show_token_name LBRACKET)
                    (show_pos pos) ) )
      in
      let cases, toks =
        match toks with
        | (ASSIGN, _) :: toks -> parse_cases toks
        | _ -> ([], toks)
      in
      ({name= {value= s; position= p}; params; cases}, toks)
  | (DATA, _) :: (ID s, p) :: toks ->
      let cases, toks =
        match toks with
        | (ASSIGN, _) :: toks -> parse_cases toks
        | _ -> ([], toks)
      in
      ({name= {value= s; position= p}; params= []; cases}, toks)
  | (DATA, _) :: (x, p) :: _ | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_data_defn failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_data_defn failed at end of input")
