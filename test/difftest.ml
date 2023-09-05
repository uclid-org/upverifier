open Printf

type diffresult =
  { program: string
  ; expected: (string, string) result option
  ; interpreter: (string, string) result }

type partial_success = {interpreter_agrees: bool}

let wipe_tmp () =
  let tmpdir = "/tmp/smpc" in
  let rec rmrf path =
    if Sys.is_directory path then (
      Sys.readdir path
      |> Array.iter (fun name -> rmrf (Filename.concat path name)) ;
      Unix.rmdir path )
    else Sys.remove path
  in
  if Sys.file_exists tmpdir then rmrf tmpdir else () ;
  Unix.mkdir tmpdir 0o777

let indent s =
  String.split_on_char '\n' s
  |> List.map (fun s -> "\t" ^ s)
  |> String.concat "\n"

let display_diffresult {program; expected; interpreter} : string =
  let display_outputs outputs =
    outputs
    |> List.map (fun (source, output) ->
           let descriptor, output =
             match output with
             | Ok output -> ("output", output)
             | Error error -> ("error", error)
           in
           sprintf "%s %s:\n\n%s" source descriptor (indent output) )
    |> String.concat "\n\n"
  in
  let expected =
    match expected with
    | Some expected -> [("Expected", expected)]
    | None -> []
  and actual = [("Interpreter", interpreter)] in
  sprintf "Program:\n\n%s\n\n" (indent program)
  ^ display_outputs (expected @ actual)

let interpreter_output_matches expected actual =
  match (expected, actual) with
  | Ok expected, Ok actual -> String.equal expected actual
  | Error _, Error _ -> true
  | Ok _, Error _ | Error _, Ok _ -> false

let result_of_diffresult diffresult =
  let ok, partial_success =
    match diffresult with
    | {program= _; expected= Some expected; interpreter} ->
        let interpreter_agrees =
          interpreter_output_matches expected interpreter
        in
        (interpreter_agrees, Some {interpreter_agrees})
    | {program= _; expected= None; interpreter= Ok _} -> (true, None)
    | {program= _; expected= None; interpreter= _} -> (false, None)
  in
  let summary = display_diffresult diffresult in
  if ok then Ok summary else Error (summary, partial_success)

let diff path input expected =
  let l2 =
    try Ok (Parse.parse [path]) with e -> Error (Printexc.to_string e)
  in
  let try_bind f arg =
    Result.bind arg (fun arg ->
        try f arg with e -> Error (Printexc.to_string e) )
  in
  let try_map f = try_bind (fun arg -> Ok (f arg)) in
  let interpreter =
    wipe_tmp () ;
    try_map (fun e -> Interp.run_io e input false) l2
  in
  wipe_tmp () ;
  result_of_diffresult {program= path; expected; interpreter}

let diff_anon program input expected =
  let l2 =
    try Ok (Parse.parse_string program)
    with e -> Error (Printexc.to_string e)
  in
  let try_bind f arg =
    Result.bind arg (fun arg ->
        try f arg with e -> Error (Printexc.to_string e) )
  in
  let try_map f = try_bind (fun arg -> Ok (f arg)) in
  let interpreter =
    wipe_tmp () ;
    try_map (fun e -> Interp.run_io e input false) l2
  in
  wipe_tmp () ;
  result_of_diffresult {program; expected; interpreter}

let read_file file =
  let ch = open_in file in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch ; s

let diff_file path =
  let filename = Filename.basename path in
  let expected =
    let name = Filename.remove_extension path in
    let out_file = name ^ ".out" and err_file = name ^ ".err" in
    match (Sys.file_exists out_file, Sys.file_exists err_file) with
    | false, false -> None
    | false, true ->
        let reason = read_file err_file in
        let description =
          "ERROR"
          ^ if String.length reason > 0 then sprintf ": %s" reason else ""
        in
        Some (Error description)
    | true, false -> Some (Ok (read_file out_file))
    | true, true ->
        failwith (sprintf "Expected output and error for test: %s" filename)
  in
  let in_file = Filename.remove_extension path ^ ".in" in
  let input = if Sys.file_exists in_file then read_file in_file else "" in
  diff path input expected

let literal_newlines x = (Str.global_replace (Str.regexp "\\\\n") "\n") x

let tsv_results =
  (try read_file "./anonymous.tsv" with _ -> "")
  |> String.split_on_char '\n'
  |> List.filter (fun line -> String.length line != 0)
  |> List.map (String.split_on_char '\t')
  |> List.map (List.map String.trim)
  |> List.mapi (fun i ->
         let name = sprintf "anonymous-%d" i in
         function
         | [program] -> [(name, diff_anon program "" None)]
         | [program; (("error" | "ERROR") as error)] ->
             [(name, diff_anon program "" (Some (Error error)))]
         | [program; expected] ->
             let output = literal_newlines expected in
             [(name, diff_anon program "" (Some (Ok output)))]
         | [program; input; (("error" | "ERROR") as error)] ->
             [(name, diff_anon program input (Some (Error error)))]
         | [program; input; expected] ->
             let output = literal_newlines expected in
             [(name, diff_anon program input (Some (Ok output)))]
         | program :: pairs ->
             let rec diff_multiple i = function
               | [] -> []
               | input :: expected :: rest ->
                   let name = sprintf "%s-%d" name i
                   and expected =
                     match expected with
                     | ("error" | "ERROR") as error -> Error error
                     | output -> Ok (literal_newlines output)
                   in
                   let result = diff_anon program input (Some expected) in
                   (name, result) :: diff_multiple (i + 1) rest
               | _ -> failwith "invalid 'anonymous.tsv' format"
             in
             diff_multiple 0 pairs
         | _ -> failwith "invalid 'anonymous.tsv' format" )
  |> List.concat

let file_results =
  Sys.readdir "./named" |> Array.to_list
  |> List.filter (fun file -> Filename.check_suffix file ".smp")
  |> List.map (sprintf "named/%s")
  |> List.map (fun f -> (f, diff_file (sprintf "./%s" f)))

let results = file_results @ tsv_results

let interp_passes res =
  match res with
  | Ok _ -> true
  | Error (_, Some partial) -> partial.interpreter_agrees
  | Error (_, None) -> false

let difftest () =
  printf "TESTING\n" ;
  results
  |> List.iter (function
       | name, Error (summary, _) ->
           printf "\n=== Test failed: %s ===\n\n%s\n" name summary
       | _, Ok _ -> () ) ;
  let num_tests = List.length results in
  let count f l =
    List.fold_left (fun count x -> if f x then 1 + count else count) 0 l
  in
  let failed_tests = count (fun (_, res) -> Result.is_error res) results in
  let interp_passed = count (fun (_, res) -> interp_passes res) results in
  if failed_tests = 0 then printf "PASSED %d tests\n" num_tests
  else
    printf "\nFAILED %d/%d tests\n(Interpreter passed %d/%d tests)"
      failed_tests num_tests interp_passed num_tests

let difftest_json () =
  List.map
    (fun (name, result) ->
      let result, summary, misc =
        match result with
        | Ok summary -> ("passed", summary, [])
        | Error (summary, partial_success) ->
            let partial_success =
              match partial_success with
              | Some {interpreter_agrees} ->
                  [("interpreter_agrees", `Bool interpreter_agrees)]
              | None -> []
            in
            ("failed", summary, partial_success)
      in
      [ ("example", `String name)
      ; ("result", `String result)
      ; ("summary", `String summary) ]
      @ misc )
    results
  |> List.map (fun results -> `Assoc results)
  |> fun elts -> `List elts

let () =
  match Sys.getenv_opt "DIFFTEST_OUTPUT" with
  | Some "json" -> difftest_json () |> Yojson.to_string |> printf "%s"
  | _ -> difftest ()
