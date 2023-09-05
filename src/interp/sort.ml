open Smtlib
open Printf

let rec display_sort = function
  | BoolSort -> "Bool"
  | IntSort -> "Int"
  | StringSort -> "String"
  | SortCall (n, []) -> n.value
  | SortCall (n, args) ->
      sprintf "%s[%s]" n.value
        (String.concat ", " (List.map display_sort args))
  | ArraySort (a, b) ->
      sprintf "Array[%s, %s]" (display_sort a) (display_sort b)
  | SeqSort a -> sprintf "Seq[%s]" (display_sort a)
