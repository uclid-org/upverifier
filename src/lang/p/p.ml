open Common
open Printf
include L3

type expr =
  | Not of expr
  | And of expr * expr
  | Or of expr * expr
  | Implies of expr * expr
  | Plus of expr * expr
  | Minus of expr * expr
  | Times of expr * expr
  | Concat of expr * expr
  | Eq of expr * expr
  | Is of expr * pstring
  | Prefix of expr * expr
  | Suffix of expr * expr
  | Contains of expr * expr
  | Lt of expr * expr
  | Lte of expr * expr
  | Gt of expr * expr
  | Gte of expr * expr
  | Let of pstring * expr * expr
  | If of expr * expr * expr option
  | Num of int
  | Str of string
  | Call of pstring * expr list
  | Const of expr * sort
  | Length of expr
  | Unit of expr
  | As of expr * sort
  | Project of pstring * expr
  | Select of expr * expr
  | Update of expr * expr * expr
  | Assign of expr * expr
  | Do of expr list
  | Forall of (pstring * sort) list * expr
  | Exists of (pstring * sort) list * expr
  | True
  | False
  | Send of expr * expr
  | Goto of pstring
  | Apply of int * pstring * expr list

type command =
  | Check
  | Push
  | Pop
  | Print of (expr, string) Either.t
  | Assume of expr
  | Assert of expr
  | Choose of
      (pstring * sort) * (pstring * sort) option * expr option * expr option
  | Fuzzed of (pstring * sort) * expr * int
  | Induction of (pstring * sort) * int * (pstring * expr) list

type fun_def =
  { name: pstring
  ; recursive: bool
  ; sort_params: pstring list
  ; params: (pstring * sort) list
  ; body: expr option
  ; sort: sort }

let is_fun (defns : fun_def list) name =
  List.exists (fun (d : fun_def) -> d.name.value = name.value) defns

let get_fun (defns : fun_def list) name =
  List.find (fun (d : fun_def) -> d.name.value = name.value) defns

let rec show_expr = function
  | Not a -> sprintf "(not %s)" (show_expr a)
  | And (a, b) -> sprintf "(%s and %s)" (show_expr a) (show_expr b)
  | Or (a, b) -> sprintf "(%s or %s)" (show_expr a) (show_expr b)
  | Implies (a, b) -> sprintf "(%s ==> %s)" (show_expr a) (show_expr b)
  | Plus (a, b) -> sprintf "(%s + %s)" (show_expr a) (show_expr b)
  | Minus (a, b) -> sprintf "(%s - %s)" (show_expr a) (show_expr b)
  | Times (a, b) -> sprintf "(%s * %s)" (show_expr a) (show_expr b)
  | Concat (a, b) -> sprintf "(%s ^ %s)" (show_expr a) (show_expr b)
  | Eq (a, b) -> sprintf "(%s = %s)" (show_expr a) (show_expr b)
  | Is (a, b) -> sprintf "(%s is %s)" (show_expr a) b.value
  | Prefix (a, b) -> sprintf "prefix(%s, %s)" (show_expr a) (show_expr b)
  | Suffix (a, b) -> sprintf "suffix(%s, %s)" (show_expr a) (show_expr b)
  | Contains (a, b) -> sprintf "contains(%s, %s)" (show_expr a) (show_expr b)
  | Lt (a, b) -> sprintf "(%s < %s)" (show_expr a) (show_expr b)
  | Lte (a, b) -> sprintf "(%s <= %s)" (show_expr a) (show_expr b)
  | Gt (a, b) -> sprintf "(%s > %s)" (show_expr a) (show_expr b)
  | Gte (a, b) -> sprintf "(%s >= %s)" (show_expr a) (show_expr b)
  | Let (a, b, c) ->
      sprintf "(let %s := %s in %s)" a.value (show_expr b) (show_expr c)
  | If (a, b, c) -> (
    match c with
    | Some els ->
        sprintf "(if %s then %s else %s)" (show_expr a) (show_expr b)
          (show_expr els)
    | None -> sprintf "(if %s then %s)" (show_expr a) (show_expr b) )
  | Num n -> sprintf "%d" n
  | Str n -> sprintf "\"%s\"" n
  | Call (f, []) -> f.value
  | Call (f, args) ->
      sprintf "%s(%s)" f.value (String.concat ", " (List.map show_expr args))
  | Length a -> sprintf "length(%s)" (show_expr a)
  | Unit a -> sprintf "unit(%s)" (show_expr a)
  | Const (a, s) -> sprintf "const(%s, %s)" (show_expr a) (show_sort s)
  | As (a, s) -> sprintf "(%s as %s)" (show_expr a) (show_sort s)
  | Project (a, b) -> sprintf "(%s.%s)" (show_expr b) a.value
  | Select (a, b) -> sprintf "(%s[%s])" (show_expr a) (show_expr b)
  | Update (a, b, c) ->
      sprintf "(%s[%s -> %s])" (show_expr a) (show_expr b) (show_expr c)
  | Assign (a, b) -> sprintf "(%s := %s)" (show_expr a) (show_expr b)
  | Do [] -> ""
  | Do [a] -> sprintf "(%s)" (show_expr a)
  | Do (a :: b) -> sprintf "(%s; %s)" (show_expr a) (show_expr (Do b))
  | Forall (params, body) ->
      sprintf "(forall (%s) %s)"
        (String.concat ", "
           (List.map (fun (x, s) -> x.value ^ " : " ^ show_sort s) params) )
        (show_expr body)
  | Exists (params, body) ->
      sprintf "(exists (%s) %s)"
        (String.concat ", "
           (List.map (fun (x, s) -> x.value ^ " : " ^ show_sort s) params) )
        (show_expr body)
  | True -> sprintf "true"
  | False -> sprintf "false"
  | Send (target, payload) ->
      sprintf "send(%s, %s)" (show_expr target) (show_expr payload)
  | Goto target -> sprintf "(goto %s)" target.value
  | Apply (count, f, args) ->
      sprintf "apply(%d, %s, %s)" count f.value
        (String.concat ", " (List.map show_expr args))

let show_command = function
  | Check -> "check"
  | Push -> "push"
  | Pop -> "pop"
  | Print (Left e) -> sprintf "print(%s)" (show_expr e)
  | Print (Right e) -> sprintf "print(%s)" e
  | Assume e -> sprintf "assume(%s)" (show_expr e)
  | Assert e -> sprintf "assert(%s)" (show_expr e)
  | Choose ((x, s1), Some (y, s2), Some a, Some b) ->
      sprintf "choose (%s: %s, %s: %s) from %s with %s" x.value
        (show_sort s1) y.value (show_sort s2) (show_expr a) (show_expr b)
  | Choose ((x, s1), None, None, Some b) ->
      sprintf "choose (%s: %s) with %s" x.value (show_sort s1) (show_expr b)
  | Choose ((x, s1), Some (y, s2), Some a, None) ->
      sprintf "choose (%s: %s, %s: %s) from %s" x.value (show_sort s1)
        y.value (show_sort s2) (show_expr a)
  | Choose ((x, s1), None, None, None) ->
      sprintf "choose (%s: %s)" x.value (show_sort s1)
  | Choose _ -> ""
  | Fuzzed ((x, s), start, times) ->
      sprintf "fuzzed (%s: %s) start %s steps %d" x.value (show_sort s)
        (show_expr start) times
  | Induction ((x, s), times, invariants) ->
      sprintf "induction (%s: %s) steps %d %s" x.value (show_sort s) times
        (String.concat " "
           (List.map
              (fun (a, b) -> sprintf "invariant %s: %s" a.value (show_expr b))
              invariants ) )

type handler_def =
  { on: (pstring * pstring) option
  ; params: (pstring * sort) list
  ; body: expr option }

type state_def = {state_name: pstring; handlers: handler_def list}

type field = pstring * sort * bool

type machine_def =
  {machine_name: pstring; fields: field list; states: state_def list}

type event_def = {event_name: pstring; payload: data}

type program =
  { funs: fun_def list
  ; sorts: sort_def list
  ; datatypes: data_def list
  ; events: event_def list
  ; machines: machine_def list
  ; sysvars: field list
  ; body: command list }
