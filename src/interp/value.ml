open Common
open Smtlib

type value =
  | Num of int
  | Bool of bool
  | Str of string
  | Array of (value * value) list * value * sort
  | Data of (string * (string * value) list)
  | Seq of value list

type environment = value symtab
