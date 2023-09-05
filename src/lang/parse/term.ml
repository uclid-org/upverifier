open Tokens
open P
open Common.Error
open Common
open Util
open Sort
open Printf

let rec parse_term in_handler toks =
  let fst, toks = parse_infix0 in_handler toks in
  let rst, toks = parse_rest_seq in_handler toks in
  match rst with [] -> (fst, toks) | _ -> (Do (fst :: rst), toks)

and parse_rest_seq in_handler toks =
  match toks with
  | (SEMICOLON, _) :: toks ->
      let e, toks = parse_infix0 in_handler toks in
      let rst, toks = parse_rest_seq in_handler toks in
      (e :: rst, toks)
  | _ -> ([], toks)

and parse_infix0 in_handler toks =
  let left, toks = parse_infix1 in_handler toks in
  match toks with
  | (ASSIGN, _) :: toks ->
      let right, toks = parse_infix0 in_handler toks in
      (Assign (left, right), toks)
  | _ -> (left, toks)

and parse_infix1 in_handler toks =
  match toks with
  | (FORALL, _) :: (LPAREN, _) :: toks ->
      let params, toks = parse_params toks in
      let body, toks = parse_infix1 in_handler toks in
      (Forall (params, body), toks)
  | (EXISTS, _) :: (LPAREN, _) :: toks ->
      let params, toks = parse_params toks in
      let body, toks = parse_infix1 in_handler toks in
      (Exists (params, body), toks)
  | _ -> parse_infix2a in_handler toks

and parse_infix2a in_handler toks =
  let left, toks = parse_infix2b in_handler toks in
  match toks with
  | (IMPLIES, _) :: toks ->
      let right, toks = parse_infix2a in_handler toks in
      (Implies (left, right), toks)
  | (IFF, _) :: toks ->
      let right, toks = parse_infix2a in_handler toks in
      (Eq (left, right), toks)
  | _ -> (left, toks)

and parse_infix2b in_handler toks =
  let left, toks = parse_infix3 in_handler toks in
  match toks with
  | (AND, _) :: toks ->
      let right, toks = parse_infix2b in_handler toks in
      (And (left, right), toks)
  | (OR, _) :: toks ->
      let right, toks = parse_infix2b in_handler toks in
      (Or (left, right), toks)
  | _ -> (left, toks)

and parse_infix3 in_handler toks =
  let left, toks = parse_infix4 in_handler toks in
  match toks with
  | (EQ, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Eq (left, right), toks)
  | (NEQ, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Not (Eq (left, right)), toks)
  | (ID "is", _) :: (ID right, p) :: toks ->
      (Is (left, {value= right; position= p}), toks)
  | (LT, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Lt (left, right), toks)
  | (LTE, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Lte (left, right), toks)
  | (GT, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Gt (left, right), toks)
  | (GTE, _) :: toks ->
      let right, toks = parse_infix3 in_handler toks in
      (Gte (left, right), toks)
  | _ -> (left, toks)

and parse_infix4 in_handler toks =
  let left, toks = parse_infix5 in_handler toks in
  match toks with
  | (PLUS, _) :: toks ->
      let right, toks = parse_infix4 in_handler toks in
      (Plus (left, right), toks)
  | (MINUS, _) :: toks ->
      let right, toks = parse_infix4 in_handler toks in
      (Minus (left, right), toks)
  | _ -> (left, toks)

and parse_infix5 in_handler toks =
  let left, toks = parse_prefix0 in_handler toks in
  match toks with
  | (TIMES, _) :: toks ->
      let right, toks = parse_infix5 in_handler toks in
      (Times (left, right), toks)
  | (CONCAT, _) :: toks ->
      let right, toks = parse_infix5 in_handler toks in
      (Concat (left, right), toks)
  | _ -> (left, toks)

and parse_prefix0 in_handler toks =
  match toks with
  | (MINUS, _) :: toks ->
      let expr, toks = parse_as in_handler toks in
      (Minus (Num 0, expr), toks)
  | (NOT, _) :: toks ->
      let expr, toks = parse_as in_handler toks in
      (Not expr, toks)
  | _ -> parse_as in_handler toks

and parse_as in_handler toks =
  let left, toks = parse_indexes_or_dots in_handler toks in
  match toks with
  | (ID "as", _) :: toks ->
      let sort, toks = parse_sort toks in
      (As (left, sort), toks)
  | _ -> (left, toks)

and parse_indexes_or_dots in_handler toks =
  let fst, toks = parse_pseudoatom in_handler toks in
  let after, toks = parse_rest_indexes_or_dots in_handler toks in
  match after with
  | [] -> (fst, toks)
  | _ ->
      ( List.fold_left
          (fun acc x ->
            match x with
            | Either.Left x -> Select (acc, x)
            | Either.Right x -> Project (x, acc) )
          fst after
      , toks )

and parse_rest_indexes_or_dots in_handler toks =
  match toks with
  | (LBRACKET, _) :: toks ->
      let index, toks = parse_term in_handler toks in
      let toks = consume_token RBRACKET toks in
      let rst, toks = parse_rest_indexes_or_dots in_handler toks in
      (Either.Left index :: rst, toks)
  | (DOT, _) :: (ID f, p) :: toks ->
      let e = {value= f; position= p} in
      let rst, toks = parse_rest_indexes_or_dots in_handler toks in
      (Either.Right e :: rst, toks)
  | _ -> ([], toks)

and parse_pseudoatom in_handler toks =
  match toks with
  | (LPAREN, _) :: toks ->
      let expr, toks = parse_term in_handler toks in
      let toks = consume_token RPAREN toks in
      (expr, toks)
  | (BAR, _) :: toks ->
      let expr, toks = parse_term in_handler toks in
      let toks = consume_token BAR toks in
      (Length expr, toks)
  | (ID "prefix", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg1, toks = parse_term in_handler toks in
      let toks = consume_token COMMA toks in
      let arg2, toks = parse_term in_handler toks in
      let toks = consume_token RPAREN toks in
      (Prefix (arg1, arg2), toks)
  | (ID "suffix", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg1, toks = parse_term in_handler toks in
      let toks = consume_token COMMA toks in
      let arg2, toks = parse_term in_handler toks in
      let toks = consume_token RPAREN toks in
      (Suffix (arg1, arg2), toks)
  | (ID "contains", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg1, toks = parse_term in_handler toks in
      let toks = consume_token COMMA toks in
      let arg2, toks = parse_term in_handler toks in
      let toks = consume_token RPAREN toks in
      (Contains (arg1, arg2), toks)
  | (ID "unit", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg, toks = parse_term in_handler toks in
      let toks = consume_token RPAREN toks in
      (Unit arg, toks)
  | (ID "const", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let arg, toks = parse_term in_handler toks in
      let toks = consume_token COMMA toks in
      let sort, toks = parse_sort toks in
      let toks = consume_token RPAREN toks in
      (Const (arg, sort), toks)
  | (ID "apply", _) :: toks ->
      let toks = consume_token LPAREN toks in
      let i, toks =
        match toks with
        | (NUM i, _) :: toks -> (i, toks)
        | (t, _) :: _ ->
            raise
              (ParseError
                 (sprintf "parse_apply failed. Expected a number but got %s"
                    (show_token_name t) ) )
        | _ ->
            raise
              (ParseError
                 "parse_apply failed. Expected a number but got end of input"
              )
      in
      let toks = consume_token COMMA toks in
      let (f, p), toks =
        match toks with
        | (ID f, p) :: toks -> ((f, p), toks)
        | (t, _) :: _ ->
            raise
              (ParseError
                 (sprintf "parse_apply failed. Expected a name but got %s"
                    (show_token_name t) ) )
        | _ ->
            raise
              (ParseError
                 "parse_apply failed. Expected a name but got end of input"
              )
      in
      let toks = consume_token COMMA toks in
      let args, toks = parse_args in_handler toks in
      (Apply (i, {value= f; position= p}, args), toks)
  | (ID f, p) :: (LPAREN, _) :: toks ->
      let args, toks = parse_args in_handler toks in
      (Call ({value= f; position= p}, args), toks)
  | (ID "send", _) :: toks when in_handler ->
      let target, toks = parse_term false toks in
      let toks = consume_token COMMA toks in
      let payload, toks = parse_pseudoatom false toks in
      (Send (target, payload), toks)
  | (ID "goto", _) :: (ID s, p) :: toks when in_handler ->
      (Goto {value= s; position= p}, toks)
  | (IF, _) :: toks -> (
      let test_expr, toks = parse_term in_handler toks in
      let toks = consume_token THEN toks in
      let then_expr, toks = parse_term in_handler toks in
      match toks with
      | (ELSE, _) :: _ ->
          let toks = consume_token ELSE toks in
          let else_expr, toks = parse_term in_handler toks in
          (If (test_expr, then_expr, Some else_expr), toks)
      | _ -> (If (test_expr, then_expr, None), toks) )
  | (LET, _) :: (ID s, p) :: toks ->
      let toks = consume_token ASSIGN toks in
      let expr, toks = parse_term in_handler toks in
      let toks = consume_id (ID "in") toks in
      let body, toks = parse_term in_handler toks in
      (Let ({value= s; position= p}, expr, body), toks)
  | [] -> raise (ParseError "parse_psuedoatom failed at end of input")
  | _ -> parse_atom toks

and parse_atom toks =
  match toks with
  | (NUM n, _) :: toks -> (Num n, toks)
  | (STR x, _) :: toks -> (Str x, toks)
  | (ID x, p) :: toks -> (Call ({value= x; position= p}, []), toks)
  | (TRUE, _) :: toks -> (True, toks)
  | (FALSE, _) :: toks -> (False, toks)
  | [] -> raise (ParseError "parse_atom failed at end of input")
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_atom failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )

and parse_args in_handler toks =
  match toks with
  | (RPAREN, _) :: toks -> ([], toks)
  | _ ->
      let arg, toks = parse_term in_handler toks in
      let rest, toks = parse_rest_args in_handler toks in
      (arg :: rest, toks)

and parse_rest_args in_handler toks =
  match toks with
  | (RPAREN, _) :: toks -> ([], toks)
  | (COMMA, _) :: toks ->
      let expr, toks = parse_term in_handler toks in
      let rest, toks = parse_rest_args in_handler toks in
      (expr :: rest, toks)
  | (x, p) :: _ ->
      raise
        (ParseError
           (sprintf "parse_rest_args failed at \"%s\" %s" (show_token_name x)
              (show_pos p) ) )
  | _ -> raise (ParseError "parse_rest_args failed at end of input")
