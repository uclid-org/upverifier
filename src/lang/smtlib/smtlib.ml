open Printf
open Common

type sort =
  | SeqSort of sort
  | ArraySort of sort * sort
  | SortCall of pstring * sort list
  | IntSort
  | BoolSort
  | StringSort

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
  | If of expr * expr * expr
  | Num of int
  | Str of string
  | Call of pstring * expr list
  | Length of expr
  | Unit of expr
  | Const of expr * sort
  | As of expr * sort
  | Project of pstring * expr
  | Select of expr * expr
  | Update of expr * expr * expr
  | Forall of (pstring * sort) list * expr
  | Exists of (pstring * sort) list * expr
  | True
  | False

type command =
  | Check
  | Push
  | Pop
  | Print of (expr, string) Either.t
  | Assume of expr
  | Assert of expr
  | Choose of
      (pstring * sort) * (pstring * sort) option * expr option * expr option

type fun_def =
  { name: pstring
  ; recursive: bool
  ; params: (pstring * sort) list
  ; body: expr option
  ; sort: sort }

type sort_def = {name: pstring; params: pstring list; body: sort}

type data = pstring * (pstring * sort) list

type data_def = {name: pstring; params: pstring list; cases: data list}

type program =
  {funs: fun_def list; datatypes: data_def list; body: command list}

let is_fun (defns : fun_def list) name =
  List.exists (fun (d : fun_def) -> d.name.value = name.value) defns

let get_fun (defns : fun_def list) name =
  List.find (fun (d : fun_def) -> d.name.value = name.value) defns

let is_sort (defns : sort_def list) name =
  List.exists (fun (d : sort_def) -> d.name.value = name.value) defns

let get_sort (defns : sort_def list) name =
  List.find (fun (d : sort_def) -> d.name.value = name.value) defns

let is_data (defns : data_def list) name =
  List.exists (fun (d : data_def) -> d.name.value = name.value) defns

let is_enum (defns : data_def list) name =
  List.exists
    (fun (d : data_def) ->
      d.name.value = name.value
      && List.length d.cases > 0
      && List.for_all (fun c -> List.length (snd c) = 0) d.cases )
    defns

let get_data (defns : data_def list) name =
  List.find (fun (d : data_def) -> d.name.value = name.value) defns

let is_cons (defns : data_def list) name =
  List.exists
    (fun (d : data_def) ->
      List.exists (fun case -> (fst case).value = name.value) d.cases )
    defns

let get_cons_defn (defns : data_def list) name =
  List.find
    (fun (d : data_def) ->
      List.exists (fun case -> (fst case).value = name.value) d.cases )
    defns

let get_cons_case (defns : data_def list) name =
  let defn = get_cons_defn defns name in
  List.find (fun case -> (fst case).value = name.value) defn.cases

let is_sel (defns : data_def list) name =
  List.exists
    (fun (d : data_def) ->
      List.exists
        (fun case ->
          List.exists (fun sel -> (fst sel).value = name.value) (snd case) )
        d.cases )
    defns

let get_sel_defn (defns : data_def list) name =
  List.find
    (fun (d : data_def) ->
      List.exists
        (fun case ->
          List.exists (fun sel -> (fst sel).value = name.value) (snd case) )
        d.cases )
    defns

let get_sel_case (defns : data_def list) name =
  let defn = get_sel_defn defns name in
  List.find
    (fun case ->
      List.exists (fun sel -> (fst sel).value = name.value) (snd case) )
    defn.cases

let get_sel_sort (defns : data_def list) name =
  let sels = snd (get_sel_case defns name) in
  let pair = List.find (fun sel -> (fst sel).value = name.value) sels in
  snd pair

let get_funs_from_commands cmds =
  List.flatten
    (List.map
       (fun c ->
         match c with
         | Choose ((x, sx), ys, _, _) ->
             let x_fun =
               {name= x; recursive= false; params= []; body= None; sort= sx}
             in
             x_fun
             ::
             ( match ys with
             | Some (y, sy) ->
                 [ { name= y
                   ; recursive= false
                   ; params= []
                   ; body= None
                   ; sort= sy } ]
             | _ -> [] )
         | _ -> [] )
       cmds )

let rec show_sort = function
  | SeqSort a -> sprintf "(Seq %s)" (show_sort a)
  | ArraySort (a, b) -> sprintf "(Array %s %s)" (show_sort a) (show_sort b)
  | SortCall (p, []) -> p.value
  | SortCall (p, args) ->
      sprintf "(%s %s)" p.value (String.concat " " (List.map show_sort args))
  | IntSort -> "Int"
  | BoolSort -> "Bool"
  | StringSort -> "String"

let rec show_expr = function
  | Not a -> sprintf "(not %s)" (show_expr a)
  | And (a, b) -> sprintf "(and %s %s)" (show_expr a) (show_expr b)
  | Or (a, b) -> sprintf "(or %s %s)" (show_expr a) (show_expr b)
  | Implies (a, b) -> sprintf "(=> %s %s)" (show_expr a) (show_expr b)
  | Plus (a, b) -> sprintf "(+ %s %s)" (show_expr a) (show_expr b)
  | Minus (a, b) -> sprintf "(- %s %s)" (show_expr a) (show_expr b)
  | Times (a, b) -> sprintf "(* %s %s)" (show_expr a) (show_expr b)
  | Concat (a, b) -> sprintf "(seq.++ %s %s)" (show_expr a) (show_expr b)
  | Eq (a, b) -> sprintf "(= %s %s)" (show_expr a) (show_expr b)
  | Prefix (a, b) ->
      sprintf "(seq.prefixof %s %s)" (show_expr a) (show_expr b)
  | Suffix (a, b) ->
      sprintf "(seq.suffixof %s %s)" (show_expr a) (show_expr b)
  | Contains (a, b) ->
      sprintf "(seq.contains %s %s)" (show_expr a) (show_expr b)
  | Lt (a, b) -> sprintf "(< %s %s)" (show_expr a) (show_expr b)
  | Lte (a, b) -> sprintf "(<= %s %s)" (show_expr a) (show_expr b)
  | Gt (a, b) -> sprintf "(> %s %s)" (show_expr a) (show_expr b)
  | Gte (a, b) -> sprintf "(>= %s %s)" (show_expr a) (show_expr b)
  | Is (a, b) -> sprintf "((_ is %s) %s)" b.value (show_expr a)
  | Let (a, b, c) ->
      sprintf "(let ((%s %s)) %s)" a.value (show_expr b) (show_expr c)
  | If (a, b, c) ->
      sprintf "(ite %s %s %s)" (show_expr a) (show_expr b) (show_expr c)
  | Num n -> sprintf "%d" n
  | Str n -> sprintf "\"%s\"" n
  | Call (f, []) -> f.value
  | Call (f, args) ->
      sprintf "(%s %s)" f.value (String.concat " " (List.map show_expr args))
  | Length a -> sprintf "(seq.len %s)" (show_expr a)
  | Unit a -> sprintf "(seq.unit %s)" (show_expr a)
  | Const (a, s) -> sprintf "((as const %s) %s)" (show_sort s) (show_expr a)
  | As (a, s) -> sprintf "(as %s %s)" (show_expr a) (show_sort s)
  | Project (a, b) -> sprintf "(%s %s)" a.value (show_expr b)
  | Select (a, b) -> sprintf "(select %s %s)" (show_expr a) (show_expr b)
  | Update (a, b, c) ->
      sprintf "(store %s %s %s)" (show_expr a) (show_expr b) (show_expr c)
  | Forall (params, body) ->
      sprintf "(forall (%s) %s)"
        (String.concat " "
           (List.map
              (fun (x, s) -> "(" ^ x.value ^ " " ^ show_sort s ^ ")")
              params ) )
        (show_expr body)
  | Exists (params, body) ->
      sprintf "(exists (%s) %s)"
        (String.concat " "
           (List.map
              (fun (x, s) -> "(" ^ x.value ^ " " ^ show_sort s ^ ")")
              params ) )
        (show_expr body)
  | True -> sprintf "true"
  | False -> sprintf "false"

let show_command = function
  | Check -> "\n(check-sat)"
  | Push -> "\n(push)"
  | Pop -> "\n(pop)"
  | Print (Left e) -> sprintf "\n(get-value (%s))" (show_expr e)
  | Print (Right e) -> sprintf "\n(echo \"%s\")" e
  | Assume e -> sprintf "\n(assert %s)" (show_expr e)
  | Assert e -> sprintf "\n(assert (not %s))" (show_expr e)
  (* print declaration part before getting to chooses here *)
  | Choose ((x, _), Some (y, _), Some a, Some b) ->
      sprintf "\n(assert (= (select %s %s) %s))\n(assert %s)" (show_expr a)
        x.value y.value (show_expr b)
  | Choose ((_, _), None, None, Some b) ->
      sprintf "\n(assert %s)" (show_expr b)
  | Choose ((x, _), Some (y, _), Some a, None) ->
      sprintf "\n(assert (= (select %s %s) %s))" (show_expr a) x.value
        y.value
  | _ -> ""

let show_selector (sel : pstring * sort) : string =
  sprintf "(%s %s)" (fst sel).value (show_sort (snd sel))

let show_case (case : data) : string =
  if List.length (snd case) = 0 then "(" ^ (fst case).value ^ ")"
  else
    let sels = String.concat " " (List.map show_selector (snd case)) in
    sprintf "(%s %s)" (fst case).value sels

let show_data_def (dfn : data_def) : string =
  match dfn.cases with
  | [] ->
      sprintf "(declare-sort %s %d)" dfn.name.value (List.length dfn.params)
  | _ ->
      let inner =
        if List.length dfn.params > 0 then
          let params =
            String.concat " " (List.map (fun x -> x.value) dfn.params)
          in
          sprintf "(par (%s)\n\t\t(%s))" params
            (String.concat "\n\t\t" (List.map show_case dfn.cases))
        else
          sprintf "(%s)"
            (String.concat "\n\t\t" (List.map show_case dfn.cases))
      in
      sprintf "(declare-datatypes (%s)\n\t(%s))"
        (sprintf "(%s %d)" dfn.name.value (List.length dfn.params))
        inner

let show_fun_def (dfn : fun_def) : string =
  match dfn.body with
  | Some body ->
      let params = String.concat " " (List.map show_selector dfn.params) in
      let cmd = if dfn.recursive then "define-fun-rec" else "define-fun" in
      sprintf "(%s %s (%s) %s\n\t%s)" cmd dfn.name.value params
        (show_sort dfn.sort) (show_expr body)
  | None ->
      let params =
        String.concat " " (List.map (fun (_, s) -> show_sort s) dfn.params)
      in
      let cmd = "declare-fun" in
      sprintf "(%s %s (%s) %s)" cmd dfn.name.value params
        (show_sort dfn.sort)

let sort_funs funs =
  List.sort
    (fun (f : fun_def) g ->
      let compare_fst = compare f.name.position.line g.name.position.line in
      if compare_fst <> 0 then compare_fst
      else compare f.name.position.column g.name.position.column )
    funs

let sort_datas datas =
  List.sort
    (fun (f : data_def) g ->
      let compare_fst = compare f.name.position.line g.name.position.line in
      if compare_fst <> 0 then compare_fst
      else compare f.name.position.column g.name.position.column )
    datas
