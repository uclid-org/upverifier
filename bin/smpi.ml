open Core
open Common.Error

let usage_msg = "smpi [-show_processed] <file1> [<file2>] ... "

let show_processed = ref false

let input_files = ref []

let output_file = ref ""

let anon_fun filename = input_files := filename :: !input_files

let speclist =
  [ ( "--show-processed"
    , Arg.Set show_processed
    , "Print program after pre-processing" ) ]

let () =
  Arg.parse speclist anon_fun usage_msg ;
  try
    if List.length !input_files > 0 then
      ignore (Interp.run_i !input_files !show_processed)
    else Printf.eprintf "Error: must specify at least one file!\n"
  with
  | Sys_error s -> Printf.eprintf "%s\n" s ; exit 1
  | TokenizerError s ->
      Printf.eprintf "Tokenizer Error: %s\n" s ;
      exit 1
  | ParseError s ->
      Printf.eprintf "Parser Error: %s\n" s ;
      exit 1
  | TypeInterpError s ->
      Printf.eprintf "Type Interp Error: %s\n" s ;
      exit 1
  | TypeMismatch s ->
      Printf.eprintf "Type Mismatch Error: %s\n" s ;
      exit 1
  | FeatureError s ->
      Printf.eprintf "Feature Mismatch Error: %s\n" s ;
      exit 1
  | ReduceUpdateError s ->
      Printf.eprintf "Reduce Update Error: %s\n" s ;
      exit 1
  | ReduceSortError s ->
      Printf.eprintf "Reduce Sort Error: %s\n" s ;
      exit 1
  | DeclarationError s ->
      Printf.eprintf "Declaration Error: %s\n" s ;
      exit 1
  | PSyntaxError s ->
      Printf.eprintf "P Syntax Error: %s\n" s ;
      exit 1
  | Stuck s ->
      Printf.eprintf "Stuck Error: %s\n" s ;
      exit 1
