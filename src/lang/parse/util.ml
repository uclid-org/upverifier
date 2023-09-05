open Tokens
open Common.Error
open Common

let consume_id i toks =
  match i with
  | ID v -> (
    match toks with
    | (ID v', _) :: toks' when v = v' -> toks'
    | [] ->
        raise
          (ParseError
             (Printf.sprintf
                "Expected \"%s\" but got to the end of the input!"
                (show_token_name i) ) )
    | (x, p) :: _ ->
        raise
          (ParseError
             (Printf.sprintf "Expected \"%s\" but got \"%s\" at %s" v
                (show_token_name x) (show_pos p) ) ) )
  | x ->
      raise
        (ParseError
           (Printf.sprintf "Expected an ID but got \"%s\"!"
              (show_token_name x) ) )

let get_id toks =
  match toks with
  | (ID v, p) :: toks' -> (v, p, toks')
  | [] ->
      raise
        (ParseError
           (Printf.sprintf "Expected an ID but got to the end of the input!")
        )
  | (x, p) :: _ ->
      raise
        (ParseError
           (Printf.sprintf "Expected and ID but got \"%s\" at %s"
              (show_token_name x) (show_pos p) ) )

let consume_token t toks =
  match toks with
  | (t', _) :: toks' when t = t' -> toks'
  | [] ->
      raise
        (ParseError
           (Printf.sprintf "Expected \"%s\" but got to the end of the input!"
              (show_token_name t) ) )
  | (x, p) :: _ ->
      raise
        (ParseError
           (Printf.sprintf "Expected \"%s\" but got \"%s\" at %s"
              (show_token_name t) (show_token_name x) (show_pos p) ) )
