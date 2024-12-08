type lamexp =
  | V of string                   
  | App of lamexp * lamexp        
  | Lam of string * lamexp        
;;

type closure = Closure of lamexp * gamma
and gamma = string -> closure option

let extend_gamma (gamma : gamma) (x : string) (cl : closure) : gamma =
  fun y -> if y = x then Some cl else gamma y

let gamma_remove x gamma =
  fun y -> if y = x then None else gamma y

let var_counter = ref 0

let fresh_var () =
  var_counter := !var_counter + 1;
  "x" ^ string_of_int !var_counter

let rec fv e =
  match e with
  | V x -> [x]
  | Lam (x, e1) -> List.filter (fun y -> y <> x) (fv e1)
  | App (e1, e2) -> (fv e1) @ (fv e2)

let rec subst e x e' =
  match e with
  | V y ->
      if y = x then e' else V y
  | Lam (y, e1) ->
      if y = x then
        Lam (y, e1)
      else if List.mem y (fv e') then
        let y' = fresh_var () in
        let e1' = subst_var e1 y y' in
        Lam (y', subst e1' x e')
      else
        Lam (y, subst e1 x e')
  | App (e1, e2) ->
      App (subst e1 x e', subst e2 x e')

and subst_var e y y' =
  match e with
  | V z ->
      if z = y then V y' else V z
  | Lam (z, e1) ->
      if z = y then
        Lam (z, e1)
      else
        Lam (z, subst_var e1 y y')
  | App (e1, e2) ->
      App (subst_var e1 y y', subst_var e2 y y')

(* Krivine machine evaluation *)
let rec evaluate (conf : closure * closure list) : closure * closure list =
  match step conf with
  | None -> conf
  | Some conf' -> evaluate conf'

and step (conf : closure * closure list) : (closure * closure list) option =
  match conf with
  | (Closure (V x, gamma), stack) ->
      (match gamma x with
       | Some cl -> Some (cl, stack)
       | None -> None)  (* Cannot proceed further *)
  | (Closure (App (e1, e2), gamma), stack) ->
      Some (Closure (e1, gamma), Closure (e2, gamma) :: stack)
  | (Closure (Lam (x, e1), gamma), cl2 :: stack) ->
      let gamma' = extend_gamma gamma x cl2 in
      Some (Closure (e1, gamma'), stack)
  | _ -> None  (* Cannot proceed further *)

(* Unload function to reconstruct the lambda term *)
let rec closure_to_exp' (Closure (e, gamma)) bound =
  match e with
  | V x ->
      if List.mem x bound then V x
      else
        (match gamma x with
         | Some cl' -> closure_to_exp' cl' bound
         | None -> V x)
  | Lam (x, e1) ->
      let bound' = x :: bound in
      Lam (x, closure_to_exp' (Closure (e1, gamma_remove x gamma)) bound')
  | App (e1, e2) ->
      App (closure_to_exp' (Closure (e1, gamma)) bound,
           closure_to_exp' (Closure (e2, gamma)) bound)

let rec unload (cl, stack) =
  match stack with
  | [] -> closure_to_exp' cl []
  | cl'::stack' ->
      App (unload (cl, stack'), closure_to_exp' cl' [])

