open List;;

type myBool = T|F;; 
let myBool2Bool b = match b with
    T -> true
  | F -> false
;;

type expb = B of myBool
          | Not of expb
          | Or of expb * expb
          | And of expb * expb
          | Iff of expb * expb
          | Imply of expb * expb
;;

let a = B T;;
let b = B F;;
let c = B T;;
let d = B F;;
let e = B T;;

let e0 = Iff ((Or (a, b)), (And ((Imply (c, d)), (Not e))));;
(*(a or b) iff ((c implies d) and (not e))*)

let not_op x = match x with
    T -> F
  | F -> T
;;

let or_op x y = match x with
    T -> T
  | F -> y
;;

let and_op x y = match x with
    F -> F
  | T -> y
;;

let imply_op x y = 
  if x = y then T
  else  y
;;

let iff_op x y = 
  if x = y then T
  else F
;;
  

let rec evalb t = match t with
    B x -> x
  | Not x -> not_op (evalb x)
  | Or (x, y) -> or_op (evalb x) (evalb y)
  | And (x, y) -> and_op (evalb x) (evalb y)
  | Imply (x, y) -> imply_op (evalb x) (evalb y)
  | Iff (x, y) -> iff_op (evalb x) (evalb y)
;;

let eval0 = evalb e0;;

if eval0 = F then print_endline "Evaluation is correct"
else print_endline "Evaluation is wrong";;


type opcodeb = LD of myBool | NOT | OR | AND | IMPLY | IFF;;

let rec compileb t = match t with
    B x -> [LD (x)]
  | Not x -> (compileb x) @ [NOT]
  | Or (x, y) -> (compileb x) @ (compileb y) @ [OR]
  | And (x, y) -> (compileb x) @ (compileb y) @ [AND]
  | Imply (x, y) -> (compileb x) @ (compileb y) @ [IMPLY]
  | Iff (x, y) -> (compileb x) @ (compileb y) @ [IFF]
;;

let com0 = compileb e0;;

exception Stuck;;

let rec stkmcb s code = match code with
    [] -> s
  | (LD(x)) :: code' -> stkmcb (x::s) code'
  | NOT :: code' -> (match s with y::s' -> let z = not_op y in stkmcb (z::s') code'
                                | _ -> raise Stuck)
  | OR :: code' -> (match s with y::w::s' -> let z = or_op y w in stkmcb (z::s') code'
                               | _ -> raise Stuck)
  | AND :: code' -> (match s with y::w::s' -> let z = and_op y w in stkmcb (z::s') code'
                                | _ -> raise Stuck)
  | IMPLY :: code' -> (match s with y::w::s' -> let z = imply_op y w in stkmcb (z::s') code'
                                  | _ -> raise Stuck)
  | IFF :: code' -> (match s with y::w::s' -> let z = iff_op y w in stkmcb (z::s') code'
                                | _ -> raise Stuck) 
;;

let calculateb e = hd (stkmcb [] (compileb e));;

let calc0 = calculateb e0;;

if calc0 = F then print_endline "Calculation is correct"
else print_endline "Calculation is wrong";;






