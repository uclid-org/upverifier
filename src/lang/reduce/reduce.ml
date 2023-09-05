open L3

let reduce l3 =
  l3 |> Sort_synonyms.reduce |> Parametric_functions.reduce
  |> Left_hand_sides.reduce |> Dos_and_assigns.reduce

let preprocess p debug =
  let out = P_syntax.reduce p in
  if debug then Printf.eprintf "%s" (show_program out) else () ;
  out
