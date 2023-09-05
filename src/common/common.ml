open Printf
module Error = Error
module Suggestion = Suggestion

module Symtab = Map.Make (struct
  type t = string

  let compare = compare
end)

type 'a symtab = 'a Symtab.t

let check_feasible = ref false

let of_list l = l |> List.to_seq |> Symtab.of_seq

let to_list st = Symtab.to_seq st

let gensym : string -> string =
  let counter = ref 0 in
  fun (base : string) ->
    let number = !counter in
    counter := !counter + 1 ;
    Printf.sprintf "%s__%d" base number

let rec input_all (ch : in_channel) : string =
  try
    let c = input_char ch in
    String.make 1 c ^ input_all ch
  with End_of_file -> ""

type pos = {line: int; column: int; file: string option}

let none_pos = {file= None; line= 0; column= 0}

let input_line_opt ic = try Some (input_line ic) with End_of_file -> None

let nth_line n filename =
  let ic = open_in filename in
  let rec aux i =
    match input_line_opt ic with
    | Some line -> if i = n then (close_in ic ; line) else aux (succ i)
    | None ->
        close_in ic ;
        failwith "end of file reached"
  in
  aux 1

let show_pos (pos : pos) =
  match pos.file with
  | Some file ->
      let description =
        sprintf "(%s: line %d, column %d)" file pos.line pos.column
      in
      let line = nth_line pos.line file in
      let below = String.make (pos.column - 1) ' ' ^ "^" in
      sprintf "%s\n\n%s\n%s\n" description line below
  | None -> sprintf "(line %d, column %d)" pos.line pos.column

type pstring = {value: string; position: pos}

let show_pstring ps = "\"" ^ ps.value ^ "\" " ^ show_pos ps.position

let count = ref 0

let mk_pstring name pos = {value= name; position= pos}

let mk_fresh_pstring name pos =
  { value=
      ( count := !count + 1 ;
        sprintf "%s__%d" name !count )
  ; position= pos }

let input_channel = ref stdin

let output_channel = ref stdout

let just_after pos = {file= None; line= pos.line; column= pos.column + 1}

let line_after pos = {file= None; line= pos.line + 1; column= -1}

let just_before pos = {file= None; line= pos.line; column= pos.column - 1}
