type clause = Fact of string | Rule of (string * string list);; 
type program = clause list;; 
type goal = string list;; 
let rec resolve_subgoal (prog: program) (subgoal: string) : (string list) list =
  match prog with
  | [] -> []
  | clause :: rest ->
      match clause with
      | Fact p ->
          if p = subgoal then
            [[]]  
          else
            resolve_subgoal rest subgoal  
      | Rule (head, body) ->
          if head = subgoal then
            body :: resolve_subgoal rest subgoal  
          else
            resolve_subgoal rest subgoal  
;;


let rec solve1 (prog: program) (goals: goal) (visited: string list) : bool =
  match goals with
  | [] -> true  
  | subgoal :: rest_goals ->
      if List.mem subgoal visited then
        false  
      else
        let substitutions = resolve_subgoal prog subgoal in
        try_substitutions prog (subgoal :: visited) rest_goals substitutions

and try_substitutions (prog: program) (visited: string list) (rest_goals: goal) (subs: (string list) list) : bool =
  match subs with
  | [] -> false  
  | sub :: rest_subs ->
      let new_goals = sub @ rest_goals in  
      if solve1 prog new_goals visited then
        true  
      else
        try_substitutions prog visited rest_goals rest_subs 
;;

let string_of_goal (g: goal) : string =
  String.concat ", " g
;;

let solve prog goal = solve1 prog goal [];;