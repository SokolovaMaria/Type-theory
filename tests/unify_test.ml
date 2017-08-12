open Hw1 
open Hw2_unify

let rec string_of_term term = 
        match term with
                | Var x -> x
                | Fun (f, args) -> f ^ "(" ^ (String.concat "," (List.map string_of_term args)) ^ ")";;

let print_solution solution = 
        List.iter (fun (x, term) -> print_string (x ^ " = " ^ (string_of_term term) ^ "\n")) solution;;

let get_and_check_solution system = 
        let solution = solve_system system in 
                match solution with 
                        | None -> print_string ("No solution\n")
                        | Some solution -> (print_solution solution; 
                                                      if (check_solution solution system) 
                                                            then print_string ("OK\n") 
                                                            else print_string("Something wrong\n"));;            

                                                              
let solvable = [(Fun("f",[Var "x"]), Fun("f",[Fun("g",[Var "y"])])); (Var "y", Fun("h",[Var "p"]))];; 
let unsolvable = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h", [Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])];; 

get_and_check_solution solvable;;
get_and_check_solution unsolvable;;

let at1 = Fun("f",[Fun("g", [Fun("t", [Var "y"])]); Fun("p", [Var "y"]); Var "y"; Fun("z", [Var"l"; Var "y"]); Var "k"]);;
match (solve_system solvable) with
        | Some solution -> print_string (string_of_term (apply_substitution solution at1))
        | None -> print_string ("no solution");;