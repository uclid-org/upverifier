open Common.Error
open Common
open Printf

type token_name =
  | SPACE
  | NEWLINE
  | LET
  | IF
  | THEN
  | ELSE
  | AND
  | OR
  | IMPLIES
  | IFF
  | FORALL
  | EXISTS
  | NOT
  | PLUS
  | MINUS
  | TIMES
  | CONCAT
  | NEQ
  | EQ
  | LT
  | LTE
  | GT
  | GTE
  | ASSIGN
  | LPAREN
  | OPENCOMMENT
  | CLOSECOMMENT
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACKET
  | RBRACKET
  | COMMA
  | SEMICOLON
  | COLON
  | BAR
  | DOT
  | ID of string
  | NUM of int
  | STR of string
  | TRUE
  | FALSE
  | TYPE
  | DATA
  | VAR
  | GHOST

let show_token_name : token_name -> string = function
  | SPACE -> " "
  | NEWLINE -> "\n"
  | LET -> "let"
  | IF -> "if"
  | THEN -> "then"
  | ELSE -> "else"
  | AND -> "and"
  | OR -> "or"
  | FORALL -> "forall"
  | EXISTS -> "exists"
  | NOT -> "not"
  | PLUS -> "+"
  | MINUS -> "-"
  | TIMES -> "*"
  | CONCAT -> "^"
  | NEQ -> "!="
  | EQ -> "="
  | LT -> "<"
  | LTE -> "<="
  | GT -> ">"
  | GTE -> ">="
  | IMPLIES -> "==>"
  | IFF -> "<==>"
  | ASSIGN -> ":="
  | OPENCOMMENT -> "(*"
  | CLOSECOMMENT -> "*)"
  | LPAREN -> "("
  | RPAREN -> ")"
  | LBRACE -> "{"
  | RBRACE -> "}"
  | LBRACKET -> "["
  | RBRACKET -> "]"
  | COMMA -> ","
  | SEMICOLON -> ";"
  | COLON -> ":"
  | BAR -> "|"
  | DOT -> "."
  | ID x -> x
  | NUM x -> string_of_int x
  | STR x -> sprintf "\"%s\"" x
  | TRUE -> "true"
  | FALSE -> "false"
  | TYPE -> "type"
  | DATA -> "data"
  | VAR -> "var"
  | GHOST -> "ghost"

let function_regex = Str.regexp "function\\b"

let bind_regex = Str.regexp "let\\b"

let in_regex = Str.regexp "in\\b"

let if_regex = Str.regexp "if\\b"

let then_regex = Str.regexp "then\\b"

let else_regex = Str.regexp "else\\b"

let and_regex = Str.regexp "and\\b"

let or_regex = Str.regexp "or\\b"

let forall_regex = Str.regexp "forall\\b"

let exists_regex = Str.regexp "exists\\b"

let not_regex = Str.regexp "not\\b"

let plus_regex = Str.regexp "\\+"

let minus_regex = Str.regexp "-"

let times_regex = Str.regexp "\\*"

let concat_regex = Str.regexp "\\^"

let neq_regex = Str.regexp "!="

let eq_regex = Str.regexp "="

let assign_regex = Str.regexp ":="

let lt_regex = Str.regexp "<"

let lte_regex = Str.regexp "<="

let gt_regex = Str.regexp ">"

let gte_regex = Str.regexp ">="

let implies_regex = Str.regexp "==>"

let iff_regex = Str.regexp "<==>"

let lparen_regex = Str.regexp "("

let rparen_regex = Str.regexp ")"

let lbrace_regex = Str.regexp "{"

let rbrace_regex = Str.regexp "}"

let lbracket_regex = Str.regexp "\\["

let rbracket_regex = Str.regexp "\\]"

let comma_regex = Str.regexp ","

let semicolon_regex = Str.regexp ";"

let colon_regex = Str.regexp ":"

let bar_regex = Str.regexp "|"

let dot_regex = Str.regexp "\\."

let whitespace_regex = Str.regexp "[ \t]+"

let newline_regex = Str.regexp "[\n]+"

let id_regex = Str.regexp "\\([A-Za-z][A-Za-z0-9_]*\\)\\b"

let underscore_regex = Str.regexp "_"

let num_regex = Str.regexp "\\(-?[0-9]+\\)\\b"

let str_regex = Str.regexp "\"\\(.*\\)\""

let tt_regex = Str.regexp "true\\b"

let ff_regex = Str.regexp "false\\b"

let int_regex = Str.regexp "Int\\b"

let bool_regex = Str.regexp "Bool\\b"

let type_regex = Str.regexp "type\\b"

let data_regex = Str.regexp "data\\b"

let var_regex = Str.regexp "var\\b"

let ghost_regex = Str.regexp "ghost\\b"

let rec_regex = Str.regexp "recursive\\b"

let is_regex = Str.regexp "is\\b"

let print_regex = Str.regexp "print\\b"

let assume_regex = Str.regexp "assume\\b"

let assert_regex = Str.regexp "assert\\b"

let open_comment_regex = Str.regexp "(\\*"

let close_comment_regex = Str.regexp "\\*)"

let get_token : string -> int -> (token_name * int) option =
 fun s index ->
  if Str.string_match open_comment_regex s index then
    Some (OPENCOMMENT, Str.match_end ())
  else if Str.string_match close_comment_regex s index then
    Some (CLOSECOMMENT, Str.match_end ())
  else if Str.string_match whitespace_regex s index then
    Some (SPACE, Str.match_end ())
  else if Str.string_match newline_regex s index then
    Some (NEWLINE, Str.match_end ())
  else if Str.string_match bind_regex s index then
    Some (LET, Str.match_end ())
  else if Str.string_match if_regex s index then Some (IF, Str.match_end ())
  else if Str.string_match then_regex s index then
    Some (THEN, Str.match_end ())
  else if Str.string_match else_regex s index then
    Some (ELSE, Str.match_end ())
  else if Str.string_match tt_regex s index then Some (TRUE, Str.match_end ())
  else if Str.string_match ff_regex s index then
    Some (FALSE, Str.match_end ())
  else if Str.string_match and_regex s index then Some (AND, Str.match_end ())
  else if Str.string_match or_regex s index then Some (OR, Str.match_end ())
  else if Str.string_match forall_regex s index then
    Some (FORALL, Str.match_end ())
  else if Str.string_match exists_regex s index then
    Some (EXISTS, Str.match_end ())
  else if Str.string_match not_regex s index then Some (NOT, Str.match_end ())
  else if Str.string_match plus_regex s index then
    Some (PLUS, Str.match_end ())
  else if Str.string_match minus_regex s index then
    Some (MINUS, Str.match_end ())
  else if Str.string_match times_regex s index then
    Some (TIMES, Str.match_end ())
  else if Str.string_match concat_regex s index then
    Some (CONCAT, Str.match_end ())
  else if Str.string_match num_regex s index then
    Some (NUM (int_of_string (Str.matched_group 1 s)), Str.match_end ())
  else if Str.string_match str_regex s index then
    Some (STR (Str.matched_group 1 s), Str.match_end ())
  else if Str.string_match lte_regex s index then Some (LTE, Str.match_end ())
  else if Str.string_match lt_regex s index then Some (LT, Str.match_end ())
  else if Str.string_match gte_regex s index then Some (GTE, Str.match_end ())
  else if Str.string_match gt_regex s index then Some (GT, Str.match_end ())
  else if Str.string_match implies_regex s index then
    Some (IMPLIES, Str.match_end ())
  else if Str.string_match iff_regex s index then Some (IFF, Str.match_end ())
  else if Str.string_match assign_regex s index then
    Some (ASSIGN, Str.match_end ())
  else if Str.string_match neq_regex s index then Some (NEQ, Str.match_end ())
  else if Str.string_match eq_regex s index then Some (EQ, Str.match_end ())
  else if Str.string_match lparen_regex s index then
    Some (LPAREN, Str.match_end ())
  else if Str.string_match rparen_regex s index then
    Some (RPAREN, Str.match_end ())
  else if Str.string_match lbrace_regex s index then
    Some (LBRACE, Str.match_end ())
  else if Str.string_match rbracket_regex s index then
    Some (RBRACKET, Str.match_end ())
  else if Str.string_match lbracket_regex s index then
    Some (LBRACKET, Str.match_end ())
  else if Str.string_match rbrace_regex s index then
    Some (RBRACE, Str.match_end ())
  else if Str.string_match comma_regex s index then
    Some (COMMA, Str.match_end ())
  else if Str.string_match semicolon_regex s index then
    Some (SEMICOLON, Str.match_end ())
  else if Str.string_match colon_regex s index then
    Some (COLON, Str.match_end ())
  else if Str.string_match bar_regex s index then Some (BAR, Str.match_end ())
  else if Str.string_match dot_regex s index then Some (DOT, Str.match_end ())
  else if Str.string_match type_regex s index then
    Some (TYPE, Str.match_end ())
  else if Str.string_match data_regex s index then
    Some (DATA, Str.match_end ())
  else if Str.string_match var_regex s index then Some (VAR, Str.match_end ())
  else if Str.string_match ghost_regex s index then
    Some (GHOST, Str.match_end ())
  else if Str.string_match id_regex s index then
    Some (ID (Str.matched_group 1 s), Str.match_end ())
  else if Str.string_match underscore_regex s index then
    Some (ID (Common.gensym "UNDERSCORE"), Str.match_end ())
  else None

type token = token_name * pos

type state = InComment of pos | OutComment

let tokenize_string (file : string option) : string -> token list =
 fun s ->
  let rec helper : pos -> state -> int -> token list =
   fun pos state index ->
    if index >= String.length s then
      match state with
      | InComment p ->
          raise
            (ParseError
               (sprintf "Comment opened but not closed! %s" (show_pos p)) )
      | _ -> []
    else
      let prev_i = index in
      let token, index =
        match get_token s index with
        | Some (x, y) -> (x, y)
        | None when state = OutComment ->
            raise
              (TokenizerError
                 (Printf.sprintf "Unknown token %s" (show_pos pos)) )
        | None -> (ID "Unknown Token", index + 1)
      in
      let x = index - prev_i in
      let new_pos =
        {line= pos.line; column= pos.column + x; file= pos.file}
      in
      match (token, state) with
      | SPACE, _ -> helper new_pos state index
      | NEWLINE, _ ->
          helper {line= pos.line + x; column= 1; file= pos.file} state index
      | OPENCOMMENT, InComment _ ->
          raise
            (TokenizerError
               (Printf.sprintf
                  "Trying to start a comment inside of a comment! %s"
                  (show_pos pos) ) )
      | OPENCOMMENT, _ -> helper new_pos (InComment pos) index
      | CLOSECOMMENT, OutComment ->
          raise
            (TokenizerError
               (Printf.sprintf
                  "Trying to close a comment that was never opned! %s"
                  (show_pos pos) ) )
      | CLOSECOMMENT, _ -> helper new_pos OutComment index
      | token, OutComment -> (token, pos) :: helper new_pos state index
      | _, InComment _ -> helper new_pos state index
  in
  helper {line= 1; column= 1; file} OutComment 0

let tokenize : string list -> token list =
 fun fs ->
  let tokens =
    List.map
      (fun file ->
        let s = Core.In_channel.read_all file in
        tokenize_string (Some file) s )
      fs
  in
  List.flatten tokens
