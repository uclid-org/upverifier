open Tokens
open P
open Common.Error
open Sort
open Data
open Event
open Machine
open Fun
open Command
open Printf
open Common
open System

let rec parse_helper ds0 ds1 ds2 ds3 ds4 ds5 cmds toks =
  match toks with
  | (ID "recursive", _) :: _ | (ID "function", _) :: _ ->
      let funs, toks = parse_fun_defn toks in
      parse_helper (funs :: ds0) ds1 ds2 ds3 ds4 ds5 cmds toks
  | (TYPE, _) :: _ ->
      let sorts, toks = parse_sort_defn toks in
      parse_helper ds0 (sorts :: ds1) ds2 ds3 ds4 ds5 cmds toks
  | (DATA, _) :: _ ->
      let datatypes, toks = parse_data_defn toks in
      parse_helper ds0 ds1 (datatypes :: ds2) ds3 ds4 ds5 cmds toks
  | (ID "event", _) :: _ ->
      let events, toks = parse_event_defn toks in
      parse_helper ds0 ds1 ds2 (events :: ds3) ds4 ds5 cmds toks
  | (ID "machine", _) :: _ ->
      let machine, toks = parse_machine_defn toks in
      parse_helper ds0 ds1 ds2 ds3 (machine :: ds4) ds5 cmds toks
  | (ID "system", _) :: _ ->
      let sysvar, toks = parse_sysvar toks in
      parse_helper ds0 ds1 ds2 ds3 ds4 (sysvar :: ds5) cmds toks
  | (ID "print", _) :: _
   |(ID "assume", _) :: _
   |(ID "assert", _) :: _
   |(ID "check", _) :: _
   |(ID "induction", _) :: _
   |(ID "choose", _) :: _
   |(ID "fuzzed", _) :: _ ->
      let cmd, toks = parse_command toks in
      parse_helper ds0 ds1 ds2 ds3 ds4 ds5 (cmd :: cmds) toks
  | _ -> (ds0, ds1, ds2, ds3, ds4, ds5, cmds, toks)

let parse_program toks =
  let funs, sorts, datatypes, events, machines, sysvars, cmds, toks =
    parse_helper [] [] [] [] [] [] [] toks
  in
  if List.length toks <> 0 then
    raise
      (ParseError
         (sprintf "Failed at parse_program %s"
            (show_pos (snd (List.hd toks))) ) )
  else {funs; sorts; datatypes; events; machines; sysvars; body= cmds}

let parse fs = tokenize fs |> parse_program

let parse_string s = tokenize_string None s |> parse_program
