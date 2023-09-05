open Tokens
open P
open Common.Error
open Common
open Util
open Term
open Printf
open Sort

let rec parse_invariants toks =
  match toks with
  | (ID "invariant", _) :: (ID cons, p) :: toks ->
      let toks = consume_token COLON toks in
      let body, toks = parse_term false toks in
      let rest, toks = parse_rest_invariants toks in
      (({value= cons; position= p}, body) :: rest, toks)
  | _ -> ([], toks)

and parse_rest_invariants toks =
  match toks with
  | (ID "invariant", _) :: (ID cons, p) :: toks ->
      let toks = consume_token COLON toks in
      let body, toks = parse_term false toks in
      let rest, toks = parse_rest_invariants toks in
      (({value= cons; position= p}, body) :: rest, toks)
  | _ -> ([], toks)

let parse_command toks =
  match toks with
  | (ID "check", _) :: toks -> (Check, toks)
  | (ID "print", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg, toks = parse_term false toks in
      let toks = consume_token RPAREN toks in
      (Print (Left arg), toks)
  | (ID "assume", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg, toks = parse_term false toks in
      let toks = consume_token RPAREN toks in
      (Assume arg, toks)
  | (ID "assert", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg, toks = parse_term false toks in
      let toks = consume_token RPAREN toks in
      (Assert arg, toks)
  | (ID "fuzzed", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let name, toks =
        match toks with
        | (ID n, p) :: toks -> ({value= n; position= p}, toks)
        | (x, p) :: _ ->
            raise
              (ParseError
                 (sprintf
                    "parse_fuzzed failed at \"%s\" %s\nExpected an identifier"
                    (show_token_name x) (show_pos p) ) )
        | _ ->
            raise
              (ParseError
                 "parse_fuzzed failed at end of input. Expected an identifier"
              )
      in
      let toks = consume_token COLON toks in
      let sx, toks = parse_sort toks in
      let toks = consume_token RPAREN toks in
      let toks = consume_id (ID "start") toks in
      let start, toks = parse_term false toks in
      let toks = consume_id (ID "steps") toks in
      let count, toks =
        match toks with
        | (NUM n, _) :: toks -> (n, toks)
        | (x, p) :: _ ->
            raise
              (ParseError
                 (sprintf
                    "parse_fuzzed failed at \"%s\" %s\nExpected a natural number"
                    (show_token_name x) (show_pos p) ) )
        | _ ->
            raise
              (ParseError
                 "parse_fuzzed failed at end of input. Expected a natural number"
              )
      in
      (Fuzzed ((name, sx), start, count), toks)
  | (ID "induction", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let name, toks =
        match toks with
        | (ID n, p) :: toks -> ({value= n; position= p}, toks)
        | (x, p) :: _ ->
            raise
              (ParseError
                 (sprintf
                    "parse_induction failed at \"%s\" %s\nExpected an identifier"
                    (show_token_name x) (show_pos p) ) )
        | _ ->
            raise
              (ParseError
                 "parse_induction failed at end of input. Expected an identifier"
              )
      in
      let toks = consume_token COLON toks in
      let sx, toks = parse_sort toks in
      let toks = consume_token RPAREN toks in
      let count, toks =
        match toks with
        | (ID "steps", _) :: toks -> (
          match toks with
          | (NUM n, _) :: toks -> (n, toks)
          | (x, p) :: _ ->
              raise
                (ParseError
                   (sprintf
                      "parse_induction failed at \"%s\" %s\nExpected a natural number"
                      (show_token_name x) (show_pos p) ) )
          | _ ->
              raise
                (ParseError
                   "parse_induction failed at end of input. Expected a natural number"
                ) )
        | _ -> (1, toks)
      in
      let invariants, toks = parse_invariants toks in
      (Induction ((name, sx), count, invariants), toks)
  | (ID "choose", _) :: (ID x, p) :: toks ->
      let toks = consume_token COLON toks in
      let sx, toks = parse_sort toks in
      let b, toks =
        match toks with
        | (ID "with", _) :: toks ->
            let b, toks = parse_term false toks in
            (Some b, toks)
        | _ -> (None, toks)
      in
      (Choose (({value= x; position= p}, sx), None, None, b), toks)
  | (ID "choose", p) :: toks ->
      let toks = consume_token LPAREN toks in
      let params, toks = parse_params toks in
      let (x, sx), ys =
        match params with
        | [(a, aa); (b, bb)] -> ((a, aa), Some (b, bb))
        | [(a, aa)] -> ((a, aa), None)
        | _ ->
            raise
              (ParseError
                 (sprintf
                    "parse_command failed. Too many parameters for choose! %s"
                    (show_pos p) ) )
      in
      let s, toks =
        match toks with
        | (ID "from", _) :: toks ->
            let s, toks = parse_term false toks in
            (Some s, toks)
        | _ -> (None, toks)
      in
      let b, toks =
        match toks with
        | (ID "with", _) :: toks ->
            let b, toks = parse_term false toks in
            (Some b, toks)
        | _ -> (None, toks)
      in
      (Choose ((x, sx), ys, s, b), toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_command failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_command failed at end of input")
