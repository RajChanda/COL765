type symbol = string;;
type signature = (symbol * int) list;;
type tree = V of string | C of { node: (symbol * int); children: tree list };;
type substitution = (string * tree) list;;

let check_sig (sig_list : signature) : bool =
  let arities_non_negative = List.for_all (fun (_, arity) -> arity >= 0) sig_list in
  let symbols = List.map fst sig_list in
  let rec has_duplicates lst =
    match lst with
    | [] -> false
    | x :: xs -> if List.mem x xs then true else has_duplicates xs
  in
  arities_non_negative && not (has_duplicates symbols)
;;

let sig1 = [("0", 0); ("1", 0); ("0", 1)];;
let sig2 = [("0", 0); ("1", 0); ("+", 2)];;
let t = C {node = ("+", 2); children = [(V "x"); (V "y"); (V "z")]} ;;
let t2 = C {node = ("+", 2); children = [(V "x"); (V "y")]} ;;
let t3 = C {node = ("+", 2); children = [(V "z"); t2]} ;;

let rec symbol_arity_in_sig (s : symbol) (arity : int) (sig_list : signature) : bool =
  match sig_list with
  | [] -> false
  | (sym, ar) :: rest ->
      if sym = s && ar = arity then true else symbol_arity_in_sig s arity rest
;;

let rec wftree (t : tree) (sig_list : signature) : bool =
  match t with
  | V _ -> true
  | C { node = (s, arity); children = ts } ->
      if not (symbol_arity_in_sig s arity sig_list) then false
      else if arity <> List.length ts then false
      else List.for_all (fun t' -> wftree t' sig_list) ts
;;


let rec ht (t : tree) : int =
  match t with
  | V _ -> 0
  | C { node = _; children = ts } ->
      let child_heights = List.map ht ts in
      1 + List.fold_left max 0 child_heights
;;

let rec size (t : tree) : int =
  match t with
  | V _ -> 1
  | C { node = _; children = ts } ->
      1 + List.fold_left (+) 0 (List.map size ts)
;;

let rec vars (t : tree) : string list =
  match t with
  | V x -> [x]
  | C { node = _; children = ts } ->
      let vars_list = List.map vars ts in
      let all_vars = List.flatten vars_list in
      List.sort_uniq compare all_vars
;;


let rec mirror (t : tree) : tree =
  match t with
  | V x -> V x
  | C { node = n; children = ts } ->
      let mirrored_children = List.map mirror ts in
      let reversed_children = List.rev mirrored_children in
      C { node = n; children = reversed_children }
;;
let check_subst (subst : substitution) : bool =
  let vars = List.map fst subst in
  let rec has_duplicates lst =
    match lst with
    | [] -> false
    | x :: xs -> if List.mem x xs then true else has_duplicates xs
  in
  not (has_duplicates vars)
;;

let rec subst_apply (subst : substitution) (t : tree) : tree =
  match t with
  | V x ->
      (try
         let t' = List.assoc x subst in
         subst_apply subst t'
       with Not_found -> V x)
  | C { node = n; children = ts } ->
      C { node = n; children = List.map (subst_apply subst) ts }
;;

let compose_subst (s1 : substitution) (s2 : substitution) : substitution =
  let s2' = List.map (fun (x, t) -> (x, subst_apply s1 t)) s2 in
  let s1_filtered = List.filter (fun (x, _) -> not (List.mem_assoc x s2)) s1 in
  s2' @ s1_filtered
;;


let rec subst (s : substitution) (t : tree) : tree =
  match t with
  | V x ->
      (try
         List.assoc x s
       with Not_found -> V x)
  | C { node = n; children = ts } ->
      C { node = n; children = List.map (subst s) ts }
;;



exception NOT_UNIFIABLE;;

let mgu (t1 : tree) (t2 : tree) : substitution =
  let rec unify (t1 : tree) (t2 : tree) (s : substitution) : substitution =
    let t1' = subst s t1 in
    let t2' = subst s t2 in
    match (t1', t2') with
    | (V x, V y) when x = y -> s
    | (V x, t) | (t, V x) ->
        if occurs x t then
          raise NOT_UNIFIABLE
        else
          let s' = [(x, t)] in
          compose_subst s' s
    | (C { node = n1; children = ts1 }, C { node = n2; children = ts2 }) ->
        if n1 <> n2 || List.length ts1 <> List.length ts2 then
          raise NOT_UNIFIABLE
        else
          unify_lists ts1 ts2 s
    | _ -> raise NOT_UNIFIABLE
  and unify_lists (ts1 : tree list) (ts2 : tree list) (s : substitution) : substitution =
    match (ts1, ts2) with
    | ([], []) -> s
    | (t1 :: rest1, t2 :: rest2) ->
        let s' = unify t1 t2 s in
        unify_lists rest1 rest2 s'
    | _ -> raise NOT_UNIFIABLE
  and occurs (x : string) (t : tree) : bool =
    match t with
    | V y -> x = y
    | C { node = _; children = ts } ->
        List.exists (occurs x) ts
  in
  unify t1 t2 []
;;

let rec string_of_tree (t : tree) : string =
  match t with
  | V x -> x
  | C { node = (n, arity); children = [] } -> n
  | C { node = (n, arity); children = ts } ->
      let children_str = String.concat ", " (List.map string_of_tree ts) in
      n ^ "(" ^ children_str ^ ")"
;;

(* Helper function to convert a tree to a string *)
let rec string_of_tree (t : tree) : string =
  match t with
  | V x -> x
  | C { node = (n, arity); children = [] } -> n
  | C { node = (n, arity); children = ts } ->
      let children_str = String.concat ", " (List.map string_of_tree ts) in
      n ^ "(" ^ children_str ^ ")"
;;

(* Helper function to convert a substitution to a string *)
let string_of_subst (s : substitution) : string =
  let pairs = List.map (fun (x, t) -> x ^ " -> " ^ (string_of_tree t)) s in
  String.concat ", " pairs
;;

(* Test MGU function *)
let test_mgu t1 t2 =
  try
    let s = mgu t1 t2 in
    Printf.printf "MGU of %s and %s is: %s\n"
      (string_of_tree t1)
      (string_of_tree t2)
      (string_of_subst s)
  with NOT_UNIFIABLE ->
    Printf.printf "MGU of %s and %s: NOT_UNIFIABLE\n"
      (string_of_tree t1)
      (string_of_tree t2)
;;


(* Define test trees *)
let t1 = V "x";;
let t2 = V "y";;
let t3 = C { node = ("0", 0); children = [] };;
let t4 = C { node = ("1", 0); children = [] };;
let t5 = C { node = ("+", 2); children = [V "x"; V "y"] };;
let t6 = C { node = ("+", 2); children = [t3; V "y"] };;
let t7 = C { node = ("+", 2); children = [V "z"; t5] };;
let t8 = C { node = ("+", 2); children = [V "x"; t5] };;
let t9 = C { node = ("+", 2); children = [t3; t4] };;
let t10 = C { node = ("+", 2); children = [V "x"; V "x"] };;
let t11 = C { node = ("+", 2); children = [V "x"] };;  (* Arity mismatch *)

(* Test MGU function *)
let test_mgu t1 t2 =
  try
    let s = mgu t1 t2 in
    Printf.printf "MGU of %s and %s is: %s\n" (string_of_tree t1) (string_of_tree t2) (string_of_subst s)
  with NOT_UNIFIABLE ->
    Printf.printf "MGU of %s and %s: NOT_UNIFIABLE\n" (string_of_tree t1) (string_of_tree t2)
;;

(* Running the test cases *)
test_mgu t1 t2;;                                  (* Test case 1 *)
test_mgu t1 t3;;                                  (* Test case 2 *)
test_mgu t3 t4;;                                  (* Test case 3 *)
test_mgu t5 t11;;                                 (* Test case 4 *)
test_mgu t1 t10;;                                 (* Test case 5 *)
test_mgu t5 t6;;                                  (* Test case 6 *)
test_mgu t7 t8;;                                  (* Test case 7 *)
test_mgu t5 t9;;                                  (* Test case 8 *)

test_mgu (mirror t7) (mirror t8);;  
                                                  
                                                  
                                                  
                                                  
                                                  
