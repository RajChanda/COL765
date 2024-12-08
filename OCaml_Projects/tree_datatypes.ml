open List;;

type exp = N of int
         | Plus of exp *  exp
         | Times of exp * exp
;;

let e0 = Plus(N 3 , Times(N 4, N 6));; 

let rec size t = match t with
    N _ -> 1
  | Plus(t1, t2) -> (size t1) + (size t2) + 1
  | Times(t1, t2) -> (size t1) + (size t2) + 1
;;

let sz0 = size e0;;

let rec height t = match t with
    N _ -> 1
  | Plus(t1, t2) -> max (height t1) (height t2) + 1
  | Times(t1, t2) -> max (height t1) (height t2) + 1
;;

let h0 = height e0;;

let rec eval t = match t with
    N x -> x
  | Plus(t1, t2) -> (eval t1) + (eval t2)
  | Times(t1, t2) -> (eval t1) * (eval t2)
;;

let eval0 = eval e0;;


type opcode = LD of int | PLUS | TIMES;;

let rec compile t = match t with
    N x -> [LD (x)]
  | Plus(t1, t2) -> (compile t1) @ (compile t2) @ [PLUS]
  | Times(t1, t2) -> (compile t1) @ (compile t2) @ [TIMES]
;;

let com0 = compile e0;;

exception Stuck;;
let rec stkmc s code = match code with
    [] -> s
  | LD(n) :: code' -> stkmc (n::s) code'
  | PLUS :: code' -> (match s with 
        n1::n2::s' -> let n = n1 + n2 in stkmc (n::s') code'
      | _ -> raise Stuck)
  | TIMES :: code' -> (match s with 
        n1::n2::s' -> let n = n1 * n2 in stkmc (n::s') code'
      | _ -> raise Stuck)
;;

let calculate e = hd(stkmc [] (compile e));;

let value0 = calculate e0;;

               

