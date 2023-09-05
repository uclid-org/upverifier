open Common
open Command

let interp (prog : Smtlib.program) =
  let empties, rest =
    List.partition
      (fun c ->
        match c with Smtlib.Choose (_, _, None, None) -> true | _ -> false )
      prog.body
  in
  let starter =
    List.fold_left
      (fun acc x -> interp_command prog.funs prog.datatypes acc x)
      Symtab.empty empties
  in
  List.fold_left
    (fun acc x -> interp_command prog.funs prog.datatypes acc x)
    starter (List.rev rest)

let interp_io (prog : Smtlib.program) input =
  let input_pipe_ex, input_pipe_en = Unix.pipe () in
  let output_pipe_ex, output_pipe_en = Unix.pipe () in
  input_channel := Unix.in_channel_of_descr input_pipe_ex ;
  set_binary_mode_in !input_channel false ;
  output_channel := Unix.out_channel_of_descr output_pipe_en ;
  set_binary_mode_out !output_channel false ;
  let write_input_channel = Unix.out_channel_of_descr input_pipe_en in
  set_binary_mode_out write_input_channel false ;
  let read_output_channel = Unix.in_channel_of_descr output_pipe_ex in
  set_binary_mode_in read_output_channel false ;
  output_string write_input_channel input ;
  close_out write_input_channel ;
  let _ = interp prog in
  close_out !output_channel ;
  let r = input_all read_output_channel in
  input_channel := stdin ;
  output_channel := stdout ;
  r

let run_i filenames debug =
  let p = Parse.parse filenames in
  let l3 = Reduce.preprocess p debug in
  let _ = Check.check true l3 in
  let smtlib = Reduce.reduce l3 in
  interp smtlib

let run_io p inp debug =
  let l3 = Reduce.preprocess p debug in
  let _ = Check.check true l3 in
  let smtlib = Reduce.reduce l3 in
  interp_io smtlib inp
