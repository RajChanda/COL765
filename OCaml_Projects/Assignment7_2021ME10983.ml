(* Define the types *)
type term =
  | V of string
  | Const of string
  | Int of int
  | List of term list
  | Node of string * term list;;

type atomic_formula = string * term list;;

type clause =
  | Fact of atomic_formula
  | Rule of { head: atomic_formula; body: atomic_formula list };;

type program = clause list;;
type goal = atomic_formula list;;
type substitution = (string * term) list;;

exception NOT_UNIFIABLE;;

(* Unification functions *)
let rec occurs (x : string) (t : term) : bool =
  match t with
  | V y -> x = y
  | Const _ -> false
  | Int _ -> false
  | List ts -> List.exists (occurs x) ts
  | Node (_, ts) -> List.exists (occurs x) ts
;;

let rec subst_term (s : substitution) (t : term) : term =
  match t with
  | V x ->
      (try
         List.assoc x s
       with Not_found -> V x)
  | Const _ -> t
  | Int _ -> t
  | List ts -> List (List.map (subst_term s) ts)
  | Node (f, ts) ->
      Node (f, List.map (subst_term s) ts)
;;

let compose_subst (s1 : substitution) (s2 : substitution) : substitution =
  let s2' = List.map (fun (x, t) -> (x, subst_term s1 t)) s2 in
  let s1_filtered = List.filter (fun (x, _) -> not (List.mem_assoc x s2)) s1 in
  s2' @ s1_filtered
;;

let rec unify_terms (t1 : term) (t2 : term) (s : substitution) : substitution =
  let t1' = subst_term s t1 in
  let t2' = subst_term s t2 in
  match (t1', t2') with
  | (V x, V y) when x = y -> s
  | (V x, t) | (t, V x) ->
      if occurs x t then
        raise NOT_UNIFIABLE
      else
        compose_subst s [(x, t)]
  | (Const c1, Const c2) ->
      if c1 = c2 then s else raise NOT_UNIFIABLE
  | (Int n1, Int n2) ->
      if n1 = n2 then s else raise NOT_UNIFIABLE
  | (List l1, List l2) ->
      unify_term_lists l1 l2 s
  | (Node (f1, ts1), Node (f2, ts2)) ->
      if f1 = f2 && List.length ts1 = List.length ts2 then
        unify_term_lists ts1 ts2 s
      else
        raise NOT_UNIFIABLE
  | _ -> raise NOT_UNIFIABLE

and unify_term_lists (ts1 : term list) (ts2 : term list) (s : substitution) : substitution =
  match (ts1, ts2) with
  | ([], []) -> s
  | (t1 :: rest1, t2 :: rest2) ->
      let s' = unify_terms t1 t2 s in
      unify_term_lists rest1 rest2 s'
  | _ -> raise NOT_UNIFIABLE
;;

let unify_atomic_formulas (af1 : atomic_formula) (af2 : atomic_formula) (s : substitution) : substitution =
  let (p1, args1) = af1 in
  let (p2, args2) = af2 in
  if p1 = p2 && List.length args1 = List.length args2 then
    unify_term_lists args1 args2 s
  else
    raise NOT_UNIFIABLE
;;

(* Evaluate built-in predicates *)
let rec evaluate_builtin (pred_name : string) (args : term list) (subst : substitution) : substitution option =
  let arg_values = List.map (subst_term subst) args in
  match (pred_name, arg_values) with
  | ("is", [V x; expr]) ->
      (match evaluate_expr expr subst with
       | Some (Int n) -> Some ((x, Int n) :: subst)
       | _ -> None)
  | ("is", [Int _; _]) ->
      None  (* Left side of 'is' should be a variable *)
  | (">", [Int n1; Int n2]) ->
      if n1 > n2 then Some subst else None
  | ("<", [Int n1; Int n2]) ->
      if n1 < n2 then Some subst else None
  | (">=", [Int n1; Int n2]) ->
      if n1 >= n2 then Some subst else None
  | ("=<", [Int n1; Int n2]) ->
      if n1 <= n2 then Some subst else None
  | ("=", [t1; t2]) ->
      (try
         let s = unify_terms t1 t2 subst in
         Some s
       with NOT_UNIFIABLE -> None)
  | _ -> None

and evaluate_expr expr subst =
  match expr with
  | Int n -> Some (Int n)
  | V x ->
      (match subst_term subst expr with
       | Int n -> Some (Int n)
       | _ -> None)
  | Node (op, [t1; t2]) when List.mem op ["+"; "-"; "*"; "/"] ->
      (match (evaluate_expr t1 subst, evaluate_expr t2 subst) with
       | (Some (Int n1), Some (Int n2)) ->
           let result =
             match op with
             | "+" -> n1 + n2
             | "-" -> n1 - n2
             | "*" -> n1 * n2
             | "/" -> n1 / n2
             | _ -> failwith "Unknown operator"
           in
           Some (Int result)
       | _ -> None)
  | _ -> None
;;

(* Prove function *)
let rec prove_all (prog: program) (goals: goal) (subst: substitution) : substitution list =
  match goals with
  | [] -> [subst]
  | goal_af :: rest_goals ->
      let (pred_name, args) = goal_af in
      if is_builtin pred_name then
        (match evaluate_builtin pred_name args subst with
         | Some s -> prove_all prog rest_goals s
         | None -> [])
      else
        let rec try_clauses clauses acc =
          match clauses with
          | [] -> acc
          | clause :: rest_clauses ->
              let fresh_clause = rename_clause clause in
              (try
                 let s = unify_atomic_formulas goal_af (head_of_clause fresh_clause) subst in
                 let new_goals = (body_of_clause fresh_clause) @ rest_goals in
                 let solutions = prove_all prog new_goals s in
                 try_clauses rest_clauses (solutions @ acc)
               with NOT_UNIFIABLE ->
                 try_clauses rest_clauses acc)
        in
        try_clauses prog []
and is_builtin pred_name =
  List.mem pred_name ["is"; ">"; "<"; ">="; "=<"; "="]
and head_of_clause clause =
  match clause with
  | Fact af -> af
  | Rule { head; _ } -> head
and body_of_clause clause =
  match clause with
  | Fact _ -> []
  | Rule { body; _ } -> body
and rename_clause clause =
  let counter = ref 0 in
  let rec rename_term t =
    match t with
    | V x -> V (x ^ "_" ^ string_of_int !counter)
    | Const _ -> t
    | Int _ -> t
    | List ts -> List (List.map rename_term ts)
    | Node (f, ts) -> Node (f, List.map rename_term ts)
  in
  let rename_af (p, args) =
    (p, List.map rename_term args)
  in
  counter := !counter + 1;
  match clause with
  | Fact af -> Fact (rename_af af)
  | Rule { head; body } ->
      Rule { head = rename_af head; body = List.map rename_af body }
;;

(* Execute and print all solutions *)
let rec execute_all (prog: program) (query: goal) : unit =
  let solutions = prove_all prog query [] in
  if solutions = [] then
    Printf.printf "No\n"
  else
    List.iteri (fun idx subst ->
        Printf.printf "Solution %d:\n" (idx + 1);
        print_substitution subst;
        print_newline ()
      ) solutions
and print_substitution subst =
  let subst_nontrivial = List.filter (fun (x, t) -> V x <> t) subst in
  match subst_nontrivial with
  | [] -> ()
  | _ ->
      List.iter (fun (x, t) ->
          Printf.printf "%s = %s\n" x (string_of_term t)
        ) subst_nontrivial
and string_of_term t =
  match t with
  | V x -> x
  | Const c -> c
  | Int n -> string_of_int n
  | List ts ->
      let elements = String.concat ", " (List.map string_of_term ts) in
      "[" ^ elements ^ "]"
  | Node (f, ts) ->
      let args = String.concat ", " (List.map string_of_term ts) in
      Printf.sprintf "%s(%s)" f args
;;

(* Simplified parser functions *)
let parse_constant s =
  try Int (int_of_string s)
  with Failure _ ->
    if s = "[]" then List []
    else Const s

let parse_variable s = V s

let rec parse_term s =
  let s = String.trim s in
  if s = "[]" then List []
  else if String.length s > 0 then
    match s.[0] with
    | '[' ->
        let content = String.sub s 1 (String.length s - 2) in
        let elements = split_string_on_char ',' content in
        let terms = List.map parse_term elements in
        List terms
    | _ ->
        if s.[0] >= 'A' && s.[0] <= 'Z' then
          parse_variable s
        else
          parse_constant s
  else
    failwith "Empty term"

(* Helper function to split a string on a character *)
and split_string_on_char sep s =
  let rec aux i j acc =
    if j >= String.length s then
      let last = String.sub s i (j - i) in
      acc @ [String.trim last]
    else if s.[j] = sep then
      let part = String.sub s i (j - i) in
      aux (j + 1) (j + 1) (acc @ [String.trim part])
    else
      aux i (j + 1) acc
  in
  aux 0 0 []
;;

let parse_predicate s args =
  (s, List.map parse_term args)

let parse_fact s args =
  Fact (parse_predicate s args)

let parse_rule head_pred head_args body_preds =
  let head = parse_predicate head_pred head_args in
  let body = List.map (fun (p, a) -> parse_predicate p a) body_preds in
  Rule { head; body }
;;
