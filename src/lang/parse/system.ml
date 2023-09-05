open Tokens
open P
open Common.Error
open Common
open Sort
open Util

let parse_sysvar toks : field * (token_name * pos) list =
  match toks with
  | (ID "system", _) :: (VAR, _) :: (ID s, pos) :: toks ->
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      (({value= s; position= pos}, sort, false), toks)
  | (ID "system", _) :: (GHOST, _) :: (ID s, pos) :: toks ->
      let toks = consume_token COLON toks in
      let sort, toks = parse_sort toks in
      (({value= s; position= pos}, sort, true), toks)
  | _ -> raise (ParseError "parse_sysvar failed")
