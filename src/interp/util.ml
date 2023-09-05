open Smtlib
open Common.Error

let rec random_int_exprs count =
  if count <= 0 then []
  else if Random.int 2 = 0 then
    Num (Random.int 100) :: random_int_exprs (count - 1)
  else Num (-Random.int 100) :: random_int_exprs (count - 1)

let gen_string length =
  let gen () =
    match Random.int (26 + 26 + 10) with
    | n when n < 26 -> int_of_char 'a' + n
    | n when n < 26 + 26 -> int_of_char 'A' + n - 26
    | n -> int_of_char '0' + n - 26 - 26
  in
  let gen _ = String.make 1 (char_of_int (gen ())) in
  String.concat "" (Array.to_list (Array.init length gen))

let rec random_str_exprs count =
  if count <= 0 then []
  else Str (gen_string (Random.int 10)) :: random_str_exprs (count - 1)

let shuffle d =
  Random.self_init () ;
  let nd = List.map (fun c -> (Random.bits (), c)) d in
  let sond = List.sort compare nd in
  List.map snd sond

(* 0 attempts means has to be complete. Always do complete by default. *)
let get_instances_of_sort guesses (ds : data_def list) (s : sort) =
  Random.self_init () ;
  match s with
  | SortCall (f, _) when is_enum ds f ->
      let defn = get_data ds f in
      List.map (fun c -> Call (fst c, [])) (shuffle defn.cases)
  | BoolSort -> if Random.int 2 = 0 then [True; False] else [False; True]
  | IntSort when guesses > 0 -> random_int_exprs guesses
  | StringSort when guesses > 0 -> random_str_exprs guesses
  | _ ->
      raise
        (Stuck
           (Printf.sprintf "Failed get_instances_of_sort: %s\n" (show_sort s))
        )

let cartesian_single l l' =
  List.concat (List.map (fun e -> List.map (fun e' -> [e; e']) l') l)

let cartesian_many ls l =
  List.concat (List.map (fun e -> List.map (fun e' -> e @ [e']) l) ls)

let cartesian ls =
  match ls with
  | [a; b] -> cartesian_single a b
  | a :: b :: cs -> List.fold_left cartesian_many (cartesian_single a b) cs
  | [a] -> List.map (fun x -> [x]) a
  | [] -> []
