open Hw1
open Hw1_reduction

let eqv1 = lambda_of_string "\\x1.\\x2.\\x3.\\x4.x1 x2 x3 x4";;
let eqv2 = lambda_of_string "\\y1.\\y2.\\y3.\\y4.y1 y2 y3 y4";;
 if (is_alpha_equivalent eqv1 eqv2) then print_string ("yes\n") else print_string("no\n");; 

let lambda = lambda_of_string "(\\x.x) (\\z.((y)(z))) (y)";;
let theta = lambda_of_string "(z)";;
if (free_to_subst theta lambda "y") then print_string ("yes\n") else print_string ("no\n");;

let is_normal = lambda_of_string "((\\x.\\y.(x))) (y))";;
if (free_to_subst (lambda_of_string "(y)") (lambda_of_string "(\\x.\\y.(x))") "x") then print_string ("yes\n") else print_string ("no\n");; 
if (is_normal_form is_normal) then print_string("yes\n") else print_string("no\n");;

let eqv3 = lambda_of_string ("\\x1.\\x2.\\x3.x1 x2");;
let eqv4 = lambda_of_string ("\\y1.\\y2.\\x3.y1 y2");;
if (is_alpha_equivalent eqv3 eqv4) then print_string ("eqv\n") else print_string ("not_eqv\n");;
                                
(* Test reduction to normal form *)
let omega = lambda_of_string "(\\x.((x) (x))) (\\x.((x) (x)))";;
let reduction_tests_1 = [
    "x";    
    "\\x.y";
    "\\x.x";
    "(\\x.x)(\\z.y)";
    "(\\x.(\\x.x) (\\x.x)) (\\y.z)";
    "(\\f.\\x.f (f (f (f x)))) (\\f.\\x.f (f (f (f x))))";
    "(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";
    "(\\x.x x x) (\\x.x) (\\x.x)";
    "(\\x.x x) \\y.y y";
    "(\\x.x x) \\y.y y z";
    "((((((((\\x.\\y.\\x.y)(\\x.x)(\\x.x)(\\a.y)b)))))))";
    "(\\x.x)\\y.x";
    "x";
    "\\x.x";
    "(\\x.x) y";
    "(\\x.\\y.x) y";
    "x x x x x x x xxxxxxxxx";
    "(\\x.x x) \\x.x x";
    "(\\a.b) x";
    "\\y.(\\a.b) x";
    "(\\x.\\y.(\\a.b) x) y";
    "(\\x.\\y.(\\a.\\x.a) x) y";
    "(\\x.y) (\\xx.y) (\\xxx.yyy)";
    "((\\x.(x) (x))) ((\\x.(x) (x)))" 
];;

let reduction_tests_2 = [
    "x";    
    "\\x.y";
    "\\x.x";
    "(\\x.x)(\\z.y)";
    "(\\x.(\\x.x) (\\x.x)) (\\y.z)";
    "(\\f.\\x.f (f (f (f x)))) (\\f.\\x.f (f (f (f x))))";
    "(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";
    "(\\x.x x x) (\\x.x) (\\x.x)";
    "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";
    "\\a.\\b.a (a (a (a (a (a (a (a (a b))))))))"
];;

let test_reduction tests f = 
    let apply f t =
        f t;
        print_string " for test: ";
        print_string t;
        print_newline()
    in
    let rec ta l = match l with
        | hd :: tl -> apply f hd; ta tl
        | [] -> print_string "Done\n"; print_newline()
    in
    ta tests;;

let test_reduce_to_normal_form () = 
    let go str = 
        let a = lambda_of_string str in
        let reduced_l = Hw1_reduction.reduce_to_normal_form a in
        let is_done = is_normal_form reduced_l in
        let str2 = string_of_lambda reduced_l in 
        match is_done with
            | true -> print_string str2
            | false -> print_string "NOT IN NORMAL FORM!!! "; print_string str2
    in
    test_reduction reduction_tests_2 go;;
        

(* Normal form without memoization *)
let reduce_to_normal_form_naive lambda = 
        let rec reduce lambda = 
                if (is_normal_form lambda) then lambda
                                                          else reduce (normal_beta_reduction lambda) in 
        reduce lambda;; 

let test_reduction lambda = 
        let start1 = Sys.time() in 
        print_string("Reducing to normal form...\n"  ^ "\nResult:\n");
        let result = reduce_to_normal_form lambda in 
        (* print_string (string_of_lambda (result)); *)
        if (is_normal_form result) then print_string ("\nOK") else print_string ("\nResult isn't in normal form");
        let end1 = Sys.time() in
        Printf.printf "\nTime_MEMOIZATION: %f ms\n\n" ((end1 -. start1) *. 1000.0);
        let result1 = reduce_to_normal_form_naive lambda in 
         if (is_normal_form result1) then print_string ("\nOK") else print_string ("\nResult isn't in normal form");
        (* print_string (string_of_lambda (result1)); *)
        Printf.printf "\nTime_NAIVE: %f ms\n\n" ((Sys.time() -. end1) *. 1000.0);;

let mem1 = lambda_of_string "((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z))))((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z))))((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z))))((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z)))) ((\\y.((y) (a))) ((\\x.x) ((\\z.(\\u.u)) (z))))";;
test_reduction mem1;;

(* test_reduce_to_normal_form();; *)
(* test_reduction omega;; *)

(* Ω combinator is divergent if it has no β-normal form *)
(* test_reduction omega;;  *)
