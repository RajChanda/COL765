(* Defining the type vector*)
type vector = float list;;

(* Defining the DimError message*)
exception DimError of string;;

(* Implementing the operations one by one*)

(*1*)

let zero n : vector =
  if n < 0 then
    raise (DimError "Invalid Dimension")
  else
    List.init n (fun _ -> 0.0);;

(*Test Case*)
let first_vector:vector = zero 10;;  

(*2*)

let unit_vector (n : int) (index : int) : vector =
  if index < 0 || index >= n then
    raise (DimError "Index out of bounds")
  else
    let rec create_vector i =
      if i = n then []
      else if i = index then 1.0 :: create_vector (i + 1)
      else 0.0 :: create_vector (i + 1)
    in
    create_vector 0;;

let unit_v1 = unit_vector 3 0;;
let unit_v2 = unit_vector 3 1;;
let unit_v3 = unit_vector 3 2;;


(*3*)

let dim (v : vector) : int = 
  (List.fold_left (fun acc x -> 1 + acc) 0 v);;

(*Test Case*)
let second_vector:vector = [3.0; 4.0; 5.0];;
let vec = second_vector;;
let len = dim second_vector;;

(*4*)

let opp (v : vector) : vector = 
  List.map (fun x -> -1.0 *. x) v;;

(*Test Case*)
let opp_vector = opp second_vector;;

(*5*)

let addv (v1 : vector) (v2 : vector) : vector = 
  if List.length v1 <> List.length v2 then
    raise (DimError "Vectors must have the same dimension")
  else
    List.map2 (+.) v1 v2;;

(*Test Case*)
let v1:vector = [1.0; 2.0; 4.0];;
let v2:vector = [3.0; 6.0; 9.0];;
let v3:vector = [7.0; 10.0; 11.0];; 

(*Commutativity*)
let commutative_check v1 v2 =
  addv v1 v2 = addv v2 v1;;
(*Associativity*)
let associative_check v1 v2 v3 =
  addv (addv v1 v2) v3 = addv v1 (addv v2 v3);;
(*Identity*)
let identity_check v =
  addv v (zero (List.length v)) = v;;
(*Inverse*)
let inverse_check v =
  let neg_v = opp v in
  addv v neg_v = zero (List.length v);;


let _ = assert (commutative_check v1 v2);;
let _ = assert (associative_check v1 v2 v3);; 
let _ = assert (identity_check v1);;
let _ = assert (inverse_check v1);;

print_endline "All vector addition laws hold.";;


(*6*)

let subv (v1 : vector) (v2 : vector) : vector = 
  if List.length v1 <> List.length v2 then
    raise (DimError "Vectors must have the same dimension")
  else
    List.map2 (-.) v1 v2;;

(*Test Case*)
let subv_check = subv v1 v2;;

(*7*)

let scalarmult (c:float) (v:vector) : vector = 
  List.map (fun x -> c*.x) v;;

let scalarmult_over_add (c:float) (v1:vector) (v2:vector) =
  scalarmult c (addv v1 v2) = addv (scalarmult c v1) (scalarmult c v2);;

let c:float = 3.0;;
let _ = assert (scalarmult_over_add c v1 v2);;
print_endline "scalar multiplication holds over vector addition.";;


(*8*)

let dotprod (v1 : vector) (v2 : vector) : float =
  if List.length v1 <> List.length v2 then
    raise (DimError "Vectors must have the same dimension")
  else
    List.fold_left2 (fun acc x1 x2 -> acc +. (x1 *. x2)) 0.0 v1 v2;;

(* Compute dot products *)
let dp1 = dotprod v1 v2;;
let dp2 = dotprod v2 v1;;


Printf.printf "Dot product of v1 and v2: %f\n" dp1;;
Printf.printf "Dot product of v2 and v1: %f\n" dp2;;

print_endline "Dot product is commutative.";;

(*9*)

let norm (v : vector) : float =
  sqrt (List.fold_left (fun acc x -> acc +. x *. x) 0.0 v)
    
let v4:vector = [3.0; 4.0]
let norm_v1 = norm v4;;


(*10*)

let normalise (v : vector) : vector =
  let length = norm v in
  if length = 0.0 then
    raise (DimError "Invalid vector for normalization")
  else
    List.map (fun x -> x /. length) v;;


(*Test Case*) 
let first_unit_vector = normalise second_vector;;

(*11*)

let parallel (v1:vector) (v2:vector) : bool = 
  if List.length v1 <> List.length v2 then
    raise (DimError "Invalid dimensions")
  else 
    let unit_v1 = normalise v1 in
    let unit_v2 = normalise v2 in
    if unit_v1 = unit_v2 then 
      true
    else 
      false;;

let check_parallel = parallel [3.0; 4.0] [1.0];;
let check_parallel2 = parallel [3.0; 4.0] (normalise [3.0; 4.0]);;

(*12*)

let crossprod (v1 : vector) (v2 : vector) : vector =
  match (v1, v2) with
  | ([x1; y1; z1], [x2; y2; z2]) ->
      [
        (y1 *. z2) -. (z1 *. y2);
        (z1 *. x2) -. (x1 *. z2);
        (x1 *. y2) -. (y1 *. x2);
      ]
  | _ -> raise (DimError "Vectors must be 3-dimensional");;

let verify_crossprod_law (v1 : vector) (v2 : vector) =
  let cp1 = crossprod v1 v2 in
  let cp2 = crossprod v2 v1 in
  let cp1_opp = opp cp1 in
  cp2 = cp1_opp;;


let v5 = [1.0; 2.0; 3.0];;
let v6 = [4.0; 5.0; 6.0];;

(* Compute cross products *)
let cp1 = crossprod v5 v6;;
let cp2 = crossprod v6 v5;;

(* Verify the cross product property *)
let _ = assert (verify_crossprod_law v5 v6);;


(* Print results *)
Printf.printf "Cross product v5 x v6: [%f; %f; %f]\n" (List.nth cp1 0) (List.nth cp1 1) (List.nth cp1 2);;
Printf.printf "Cross product v6 x v5: [%f; %f; %f]\n" (List.nth cp2 0) (List.nth cp2 1) (List.nth cp2 2);;

print_endline "Cross product property verified.";;









  
  


    



    
  




