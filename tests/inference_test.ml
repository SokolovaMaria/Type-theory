open Hw1
open Hw1_reduction
open Hw2_unify
open Hw2_inference

let rec string_of_hm_type hmt = 
        match hmt with
                | HM_Elem t -> t 
                | HM_Arrow(t1, t2) -> "(" ^ (string_of_hm_type t1) ^ "->" ^ (string_of_hm_type t2) ^ ")"
                | HM_ForAll(a, t) -> "∀" ^ a ^ "." ^ (string_of_hm_type t);; 

let rec simp_type_to_algebraic_term simp_type = 
                match simp_type with
                        | S_Elem t -> Hw2_unify.Var (t)
                        | S_Arrow(a, b) -> Hw2_unify.Fun("impl", (simp_type_to_algebraic_term a) :: (simp_type_to_algebraic_term b) :: []);;

let rec string_of_term term = 
        match term with
                | Var x -> x
                | Fun (f, args) -> f ^ "(" ^ (String.concat "," (List.map string_of_term args)) ^ ")";;

let rec print_system system = 
        match system with 
                | [] -> print_string("\n")
                | (x, st) :: tail -> (print_string(x ^ " = " ^ string_of_term(simp_type_to_algebraic_term st) ^ "\n"); print_system tail) ;;                


let rec algebraic_term_to_simp_type term = 
        match term with 
                | Hw2_unify.Var x -> S_Elem(x)
                | Hw2_unify.Fun(str, head :: tail :: []) -> S_Arrow(algebraic_term_to_simp_type head, algebraic_term_to_simp_type tail) 
                | _ -> failwith("not an algebraic term");;


let lambda1 = lambda_of_string ("\\a.\\b.\\c.\\d.a (b (c d))");;
let lambda2 = lambda_of_string("(\\f.\\x.(f (f (x))))");;

let y_combinator = Abs("f", App(Abs("x", App(Var "f", App(Var "x", Var "x"))), Abs("x", App(Var "f", App(Var "x", Var "x")))));;

(* -------------------------------------------------------------- *)
let check_algorithm_w l = 
    let result = algorithm_w l in
        match result with
            None -> "Bad lambda"
            | Some (solution, solved_type) -> 
                "Type of lambda: " ^ (string_of_hm_type solved_type) ^ "\n" ^
                "Free variables: \n" ^ (String.concat "\n" (List.map (fun (name, tp) -> name ^ ": " ^ (string_of_hm_type tp)) solution));;

let rec hm_lambda_of_lambda l = match l with
    Hw1.Var a -> HM_Var a
    | App (a, b) -> HM_App (hm_lambda_of_lambda a, hm_lambda_of_lambda b)
    | Abs (var, last) -> HM_Abs (var, hm_lambda_of_lambda last);;


let t = HM_Var "t";;
let f = HM_Var "f";;
let id = HM_Var "id";;
let x = HM_Var "x";;
let y = HM_Var "y";;
let z = HM_Var "z";;
let dd = HM_Var "dd";;
let num2 = HM_Abs("f", HM_Abs ("x", HM_App (f, HM_App (f, x))));;
let t1t = HM_Let ("id", HM_Abs("x", x), HM_Abs("f", HM_Abs("x", HM_App(id, HM_App(id, HM_App(id, x))))));;
let t4t = HM_Let ("id", HM_Abs("t", t), HM_Abs("f", HM_Abs("x", HM_App(HM_App(id, f), HM_App(id, x)))));;
let t5t = HM_Let ("id", HM_Abs("t", t), HM_Abs("f", HM_Abs("x", HM_App(HM_App(id, f), HM_App (HM_App(id, f), HM_App(id, x))))));;
let t6t = HM_Let ("dd", HM_Abs("f", HM_Abs ("x", HM_App (f, HM_App (f, x)))), HM_App (dd, HM_App (dd, HM_App (dd, HM_App (dd, HM_App (dd, dd))))));;

let t7t = Abs("f", Abs ("x", App (Var "f", App (Var "f", Var "x"))));;

let y_combinator = HM_Abs("f", HM_App(HM_Abs("x", HM_App(HM_Var "f", HM_App (HM_Var "x", HM_Var "x"))), HM_Abs("x", HM_App(HM_Var "f", HM_App (HM_Var "x", HM_Var "x"))) ));;

let t8t = HM_Let ("a", num2, HM_Let ("b", num2, HM_Let ("c", num2, HM_App (HM_Var "a", HM_App (HM_Var "b", HM_Var "c")))));;

let t9 = HM_App(t, f);;

let num1 = HM_Abs("f", HM_Abs ("x", HM_App (f, x)));;
let book_test = HM_Let("id", HM_Abs("x", HM_Var "x"), HM_App(HM_Var "id", HM_Var "id"));;
print_string ((check_algorithm_w y_combinator) ^ "\n\n");;

print_string ((check_algorithm_w t6t) ^ "\n\n");;
print_string ((check_algorithm_w t5t) ^ "\n\n");;
print_string ((check_algorithm_w t8t) ^ "\n\n");;
print_string ((check_algorithm_w (HM_Abs ("f", HM_Abs ("x", HM_Let ("dd", HM_Abs ("z", HM_App (f, HM_App (f, z))), HM_App (dd, HM_App (dd, HM_App (dd, x)))))))) ^ "\n\n");; 
(* 
print_string ((check_algorithm_w (hm_lambda_of_lambda (lambda_of_string "\\f.\\x.f (f (f x))"))) ^ "\n");; *)        