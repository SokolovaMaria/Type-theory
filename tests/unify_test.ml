open Hw1 
open Hw2_unify
open List

let rec string_of_term term = 
        match term with
                | Var x -> x
                | Fun (f, args) -> f ^ "(" ^ (String.concat "," (List.map string_of_term args)) ^ ")";;

let term_to_string a = 
        let rec dfs x = 
            match x with
                | Var (var_name) -> var_name
                | Fun (fun_name, arguments) -> "(" ^ fun_name ^ 
                (List.fold_left (fun prv term ->  prv ^ " " ^ (dfs term)) "" arguments) ^ ")"
        in
        dfs a;;                

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
(* get_and_check_solution solvable;;
get_and_check_solution unsolvable;;
 *)

(* (F x) *)
let term1 = Fun ("F", [Var "x"]);;

(* (F (f a b c) (f e d c)) *)
let term2 = Fun ("F", [(Fun ("f", [(Var "a"); (Var "b"); (Var "c")])); (Fun ("f", [(Var "e"); (Var "d"); (Var "c")]))]);;

(* (F (f a b c) (f e d f) (G (G (g (H (h a b c) (h e d c)) b c)) (g e d f)) ) *)
let term3 = Fun ("F", [Fun("f", [Var "a"; Var "b"; Var "c"]); Fun("f", [Var "e"; Var "d"; Var "c"]); 
Fun ("G", [Fun("G", [
Fun ("g", [Fun ("H", [Fun("h", [Var "a"; Var "b"; Var "c"]);Fun("h", [Var "e"; Var "d"; Var "c"])]); Var "b"; Var "c"])
]) ;Fun ("g", [Var "e"; Var "d"; Var "f"])])
]);;

let rec print_subst s = 
    match s with 
        | hd :: tl -> 
            let (x, y) = hd in
            print_string (x ^ " -> " ^ (term_to_string y) ^ ", "); 
            print_subst tl
        | [] -> print_string ";"
;;

let test_solve_system () = 
    let go system =
        let sol = Hw2_unify.solve_system system in
        match sol with
        | Some x -> 
            print_subst x;
            let correct = Hw2_unify.check_solution x system in
            if correct then print_string " OK\n"
            else print_string " NOT CORRECT!\n"
        | None -> print_string "No solutions\n"
    in
    go [((Var "x"), term2)];
    go [(term2, Var "x")];
    let term1 = Fun ("F", [Fun ("g", [Var "a"; Var "b"]); Var "c"]) in
    let term2 = Fun ("F", [Var "x"; Var "y"]) in
    go [(term1, term2); (term1, term1); (term2, term2)];
    let term1 = Fun ("F", [Fun ("g", [Var "a"; Var "b"]); Var "b"]) in
    let term2 = Fun ("F", [Var "x"; Var "y"]) in
    go [(term1, term2)];
    let sys0 = [(Var "a", Var "b"); (Var "x", Var "y")] in go sys0;
    let sys1 = [(Fun("f",[Var "a"]), Fun("f",[Fun("g",[Fun("h",[Var "b"])])])); (Var "a", Var "b")] in go sys1;
    let sys2 = [(Fun("f",[Var "a"]), Var "b")] in go sys2;
    let sys3 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"])] in go sys3;
    let sys4 = [Fun("f",[Var "a"; Var "b"]), Fun("g",[Var "x"; Var "y"])] in go sys4;
    let sys5 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"; Var "z"])] in go sys5;
    let sys6 = [(Var "a", Fun("f", [Var "a"]))] in go sys6;
    let solvable = [(Fun("f",[Var "x"]), Fun("f",[Fun("g",[Var "y"])])); (Var "y", Fun("h",[Var "p"]))] in go solvable; 
    let unsolvable = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h", [Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])]
    in go unsolvable
;;

test_solve_system ();;