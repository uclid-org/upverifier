open Tokens
open P
open Common.Error
open Util
open Printf
open Common

let sort_call_or_prim (f : pstring) args _ =
  match f.value with
  | "Seq" -> (
    match args with
    | [a] -> SeqSort a
    | _ ->
        raise
          (ParseError
             (Printf.sprintf "sort_call_or_prim failed at %s"
                (show_pstring f) ) ) )
  | "Array" -> (
    match args with
    | [a; b] -> ArraySort (a, b)
    | _ ->
        raise
          (ParseError
             (Printf.sprintf "sort_call_or_prim failed at %s"
                (show_pstring f) ) ) )
  | _ -> SortCall (f, args)

let rec parse_sort toks =
  match toks with
  | (ID "Int", _) :: toks -> (IntSort, toks)
  | (ID "Bool", _) :: toks -> (BoolSort, toks)
  | (ID "String", _) :: toks -> (StringSort, toks)
  | (LPAREN, _) :: toks ->
      let expr, toks = parse_sort toks in
      let toks = consume_token RPAREN toks in
      (expr, toks)
  | (ID _, _) :: (LPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf "parse_sort failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name LPAREN) (show_pos pos)
              (show_token_name LBRACKET) ) )
  | (ID f, p) :: (LBRACKET, _) :: toks ->
      let args, toks = parse_sort_args toks in
      (sort_call_or_prim {value= f; position= p} args toks, toks)
  | (ID f, p) :: toks -> (SortCall ({value= f; position= p}, []), toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_sort failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_sort failed at end of input")

and parse_sort_args toks =
  match toks with
  | (RBRACKET, _) :: toks -> ([], toks)
  | (RPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_sort_args failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name RPAREN) (show_pos pos)
              (show_token_name RBRACKET) ) )
  | _ ->
      let arg, toks = parse_sort toks in
      let rest, toks = parse_rest_sort_args toks in
      (arg :: rest, toks)

and parse_rest_sort_args toks =
  match toks with
  | (RBRACKET, _) :: toks -> ([], toks)
  | (RPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_rest_sort_args failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name RPAREN) (show_pos pos)
              (show_token_name RBRACKET) ) )
  | (COMMA, _) :: toks ->
      let expr, toks = parse_sort toks in
      let rest, toks = parse_rest_sort_args toks in
      (expr :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_rest_sort_args failed at %s" (show_pos p)) )
  | _ -> raise (ParseError "parse_rest_sort_args failed at end of input")

let rec parse_names toks =
  match toks with
  | (RBRACKET, _) :: toks -> ([], toks)
  | (RPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf "parse_names failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name RPAREN) (show_pos pos)
              (show_token_name RBRACKET) ) )
  | (ID param, p) :: toks ->
      let rest, toks = parse_rest_names toks in
      ({value= param; position= p} :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_names failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_names failed at end of input")

and parse_rest_names toks =
  match toks with
  | (RBRACKET, _) :: toks -> ([], toks)
  | (RPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf
              "parse_rest_names failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name RPAREN) (show_pos pos)
              (show_token_name RBRACKET) ) )
  | (COMMA, _) :: (ID param, p) :: toks ->
      let rest, toks = parse_rest_names toks in
      ({value= param; position= p} :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError (sprintf "parse_rest_names failed at %s" (show_pos p)))
  | _ -> raise (ParseError "parse_rest_names failed at end of input")

let parse_sort_defn toks =
  match toks with
  | (TYPE, _) :: (LBRACKET, pos) :: toks ->
      let params, toks = parse_names toks in
      let s, p, toks =
        match toks with
        | (ID s, p) :: toks -> (s, p, toks)
        | _ ->
            raise
              (ParseError
                 (sprintf "parse_sort_defn failed at \"%s\" %s"
                    (show_token_name LBRACKET)
                    (show_pos pos) ) )
      in
      let toks = consume_token ASSIGN toks in
      let body, toks = parse_sort toks in
      ({name= {value= s; position= p}; params; body}, toks)
  | (TYPE, _) :: (LPAREN, pos) :: _ ->
      raise
        (ParseError
           (sprintf "parse_sort failed at \"%s\" %s\nDid you mean \"%s\"?"
              (show_token_name LPAREN) (show_pos pos)
              (show_token_name LBRACKET) ) )
  | (TYPE, _) :: (ID s, p) :: toks ->
      let toks = consume_token ASSIGN toks in
      let body, toks = parse_sort toks in
      ({name= {value= s; position= p}; params= []; body}, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_sort_defn failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_sort_defn failed at end of input")

let rec parse_params toks =
  match toks with
  | (RPAREN, _) :: toks -> ([], toks)
  | (ID param, p) :: (COLON, _) :: toks ->
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_params toks in
      (({value= param; position= p}, sort) :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_params failed at %s %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_params failed at end of input")

and parse_rest_params toks =
  match toks with
  | (RPAREN, _) :: toks -> ([], toks)
  | (COMMA, _) :: (ID param, p) :: (COLON, _) :: toks ->
      let sort, toks = parse_sort toks in
      let rest, toks = parse_rest_params toks in
      (({value= param; position= p}, sort) :: rest, toks)
  | (_, p) :: _ ->
      raise
        (ParseError (sprintf "parse_rest_params failed at %s" (show_pos p)))
  | _ -> raise (ParseError "parse_rest_params failed at end of input")
