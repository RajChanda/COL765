module Set =
struct
  type 'a set = 'a list

  let emptyset : 'a set = []

  let rec insert x s =
    if List.mem x s then s else x :: s

  let member x s = List.mem x s

  let subset s1 s2 =
    List.for_all (fun x -> member x s2) s1

  let equalsets s1 s2 =
    subset s1 s2 && subset s2 s1

  let union s1 s2 =
    List.fold_left (fun acc x -> insert x acc) s2 s1

  let inter s1 s2 =
    List.filter (fun x -> member x s2) s1

  let diff s1 s2 =
    List.filter (fun x -> not (member x s2)) s1

  let product s1 s2 =
    List.fold_left
      (fun acc x ->
         List.fold_left
           (fun acc' y -> insert (x, y) acc')
           acc s2)
      emptyset s1

  let power s =
    let rec powerset s =
      match s with
      | [] -> [emptyset]
      | x :: xs ->
          let ps = powerset xs in
          ps @ List.map (fun subset -> insert x subset) ps
    in
    powerset s
end;;

open Set;; 
let make_set lst =
  List.fold_left (fun acc x -> insert x acc) emptyset lst;;

let string_of_int_set s =
  "{" ^ (String.concat "; " (List.map string_of_int s)) ^ "}"

let string_of_pair_set s =
  "{" ^ (String.concat "; " (List.map (fun (a, b) -> "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")") s)) ^ "}"

