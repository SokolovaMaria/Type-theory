open Hw1

let rec is_normal_form l = match l with
    | Var x -> true
    | App(Abs(x, l1), l2) -> false
    | App(l1, l2) -> (is_normal_form l1) && (is_normal_form l2)
    | Abs(x, l2) -> is_normal_form l2;;

module SS = Set.Make(String);;

let free_vars l = 
    let rec get_fv l bound = 
        match l with
            | Var x -> if (SS.mem x bound) then SS.empty else SS.singleton x
            | App (l1, l2) ->  SS.union (get_fv l1 bound) (get_fv l2 bound)
            | Abs (x, l) -> get_fv l (SS.add x bound) in 
    let fv = get_fv l SS.empty in 
    SS.elements fv;;

(* m[x := n] *)
let free_to_subst n m x =
    let free_n = free_vars n in
    let inter a b = not (List.exists (fun x -> List.mem x a) b) in
    let add x list = (x :: list) in
    let rec check m bound_m x  =
        match m with
            | Var y -> if (x <> y) then true else (inter free_n bound_m)
            | App (p, q) -> (check p bound_m x) && (check q bound_m x)
            | Abs (y, p) -> if (x <> y) then (check p (add y bound_m) x) else true in
    check m [] x;; 

    
(* m[x := n] *)
let rec substitute n m x =
    match m with
        | Var y -> if (x = y) then n else m
        | App(p, q) -> App((substitute n p x), (substitute n q x))
        | Abs(y, p) -> if (x <> y) then Abs(y, (substitute n p x)) else m;;

 let rec is_alpha_equivalent l1 l2 = 
    let i = ref 0 in
    let get_fresh_var () = 
        let fresh_var = ("fresh" ^ string_of_int !i) in 
        i := !i + 1;
        Var(fresh_var) in

    match (l1, l2) with
        | (Var x, Var y) -> (x = y)
        | (App(p1, q1), App(p2, q2)) -> (is_alpha_equivalent p1 p2) && (is_alpha_equivalent q1 q2)
        | (Abs(x, p), Abs(y, q)) -> let fresh_var = get_fresh_var () in  
                                                   is_alpha_equivalent (substitute fresh_var p x) (substitute fresh_var q y)
        | _ -> false;; 

module StringMap = Map.Make(String);;

 let i = ref 0;;
        let get_fresh_var () = 
            let fresh_var = ("τ" ^ string_of_int !i) in 
            i := !i + 1;
            fresh_var;;

let rec get_eqv l map = 
                match l with
                    | Var x -> if (StringMap.mem x map) then Var (StringMap.find x map) else l 
                    | App(p, q) -> App(get_eqv p map, get_eqv q map)
                    | Abs(x, p) -> let fresh_var = get_fresh_var () in 
                                   Abs (fresh_var, (get_eqv p (StringMap.add x fresh_var map)));;

let get_alpha_equivalent l =
        get_eqv l StringMap.empty;;                                

let normal_beta_reduction l = 
    let rec subst_first_beta_redex lambda =
        match lambda with
            | App (Abs(x, p), q) -> (true, (substitute q p x))
            | Var x -> (false, lambda)
            | App(p, q) -> let (found_br, p1) = (subst_first_beta_redex p) in 
                                    if found_br then (true, App(p1, q))
                                                     else let (found_br, q1) = (subst_first_beta_redex q) in 
                                                               (found_br, App(p, q1))
            | Abs(x, p) -> let (found_br, p1) = (subst_first_beta_redex p) in 
                                   (found_br, Abs(x, p1)) in 
    snd ( subst_first_beta_redex (get_alpha_equivalent l) );; 


(* Get normal form of lambda, using normal reduction order with memoization *)

type ref_lambda = Var_ref of string | Abs_ref of (string * (ref_lambda ref)) | App_ref of ((ref_lambda ref) * (ref_lambda ref)) 

let rec ref_lambda_of_lambda l = 
        match l with
                | Var x -> ref (Var_ref x)
                | Abs(x, p) -> ref (Abs_ref(x, ref_lambda_of_lambda p))
                | App(p, q) -> ref (App_ref(ref_lambda_of_lambda p, ref_lambda_of_lambda q));;

let rec lambda_of_ref_lambda refl = 
        match !refl with
                | Var_ref x -> Var x
                | Abs_ref (x, p) ->  Abs(x, lambda_of_ref_lambda p)
                | App_ref (p, q) -> App (lambda_of_ref_lambda p, lambda_of_ref_lambda q);;


let rec substitute_ref what where var =
           match !where with 
                    | Var_ref x -> if (x = var) then where := !what
                    | Abs_ref(x, p) -> if (x <> var) then substitute_ref what p var 
                    | App_ref(p, q) -> substitute_ref what p var; substitute_ref what q var;;

let reduce_to_normal_form lambda = 
        let rec reduce ref_l = 
                match !ref_l with 
                        | Var_ref x -> None
                        | Abs_ref (x, p) -> (match (reduce p) with 
                                                            | Some reduced_p -> Some ref_l
                                                            | None -> None)
                        | App_ref (p, q) -> (match !p with
                                                            | Abs_ref (x, p1) -> let fresh_var = get_fresh_var () in    
                                                                                          ref_l := !(ref_lambda_of_lambda (get_eqv (lambda_of_ref_lambda p1) (StringMap.singleton x fresh_var)));
                                                                                          substitute_ref q ref_l fresh_var;
                                                                                          Some ref_l
                                                            | _ -> (match (reduce p) with
                                                                            | Some reduced_p -> Some ref_l 
                                                                            | None -> (match (reduce q) with 
                                                                                                    | Some reduced_q -> Some ref_l 
                                                                                                    | None -> None))) in
         let rec reduction_step ref_l =
                match (reduce ref_l) with
                        | Some reduced -> reduction_step reduced
                        | None -> ref_l in                
         let ref_l = ref_lambda_of_lambda (get_alpha_equivalent lambda) in 
         lambda_of_ref_lambda (reduction_step ref_l);;

 


(* let lambda1 = lambda_of_string "(\\x.y) (\\y.y) ";;
let lambda2 = lambda_of_string "((\\x.a) (\\x.a))";;
List.iter (fun var -> print_string var) (free_vars lambda2);;  *)                                    

(* Test reduction to normal form *)
(* let l1 = lambda_of_string "(\\x. (x x)) ((\\x. y) z)";;
let l2 = lambda_of_string "(\\x. x x x x) (\\x. x)";;
let l3 = lambda_of_string "(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";;
let l4 = lambda_of_string "(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))";;
let l5 = lambda_of_string "(\\y.\\m.y (\\f.\\n.(\\s.(s (\\x.\\a.\\b.b) (\\a.\\b.a)) (\\f.\\x.x) (f s)) (m n)) (\\f.\\x.f (f (f x)))) (\\f.(\\x.f (x x)) (\\x.f (x x))) ((\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)))";;
let l6 = lambda_of_string"(\\s.\\k.\\i.(((s ((s (k s)) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s ((s (k s)) ((s (k (s (k (s ((s ((s ((s i) (k (k (k i))))) (k ((s (k k)) i)))) (k ((s ((s (k s)) ((s (k k)) i))) (k i))))))))) ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k (s (k ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k k)) i))))) (k ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) (k ((s (k k)) i)))))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) (k (k ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) ((s ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i))))) ((s ((s (k s)) ((s (k (s (k s)))) ((s ((s (k s)) ((s (k (s (k s)))) ((s (k (s (k k)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s (k (s i))))) ((s (k (s (k k)))) ((s (k (s i))) ((s (k k)) i)))))))))) (k (k ((s (k k)) i))))))) (k (k (k i))))) (\\x.\\y.\\z.x z (y z)) (\\x.\\y.x) (\\x.x)";;
let l7 = lambda_of_string "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";;
let l8 = lambda_of_string "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((\\l14.((\\l15.((\\l16.((\\l17.((\\l18.(l18 (\\l19.(\\l20.(l19 (l19 (l19 (l19 (l19 (l19 (l19 (l19 (l19 l20))))))))))))) (\\l18.(l4 (((l17 l18) (\\l19.(\\l20.l20))) l18))))) (l0 (\\l17.(\\l18.(\\l19.(\\l20.(((l1 ((l9 l19) l20)) l19) ((\\l21.(((l1 ((l16 (l14 l21)) l18)) (((l17 l18) ((l6 l21) (\\l22.(\\l23.(l22 l23))))) l20)) (((l17 l18) l19) l21))) (l15 ((l6 l19) l20))))))))))) (l0 (\\l16.(\\l17.(\\l18.((l10 (l8 l17)) (((l1 (l8 l18)) l3) ((l16 ((l7 l17) (\\l19.(\\l20.(l19 l20))))) ((l7 l18) (\\l19.(\\l20.(l19 l20))))))))))))) (l0 (\\l15.(\\l16.(((l1 (l8 (l4 l16))) (\\l17.(\\l18.l18))) ((l6 (\\l17.(\\l18.(l17 l18)))) (l15 (l4 (l4 l16)))))))))) (\\l14.(\\l15.(l14 (l14 l15)))))) (\\l13.((((l0 (\\l14.(\\l15.(\\l16.(\\l17.(((l1 (l8 l15)) l17) (((l14 (l4 l15)) l17) ((l6 l16) l17)))))))) l13) (\\l14.(\\l15.l15))) (\\l14.(\\l15.(l14 l15))))))) (\\l12.(\\l13.(\\l14.((l14 l12) l13)))))) (l0 (\\l11.(\\l12.(\\l13.(((l1 (l8 l12)) (\\l14.(\\l15.l15))) ((l6 l13) ((l11 (l4 l12)) l13))))))))) (\\l10.(\\l11.(((l1 l10) l2) l11))))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";;
let l9 = lambda_of_string "((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.(l10 (\\l11.(\\l12.(l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 (l11 l12))))))))))))))))) (\\l10.((l0 (\\l11.(\\l12.((\\l13.(((l1 (l8 l13)) (\\l14.(\\l15.(l14 l15)))) ((l6 (l11 l13)) (l11 (l4 l13))))) (l4 l12))))) l10)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))";;

let omega = lambda_of_string "(\\x.((x) (x))) (\\x.((x) (x)))";;


let test_reduction lambda = 
        let start1 = Sys.time() in 
        print_string("Reducing to normal form\n" ^ string_of_lambda(lambda) ^ "\nResult:\n");
        let result = reduce_to_normal_form lambda in 
        print_string (string_of_lambda (result));
        if (is_normal_form result) then print_string ("\nOK") else print_string ("\nResult isn't in normal form");
        let end1 = Sys.time() in
        Printf.printf "\nTime_MEMOIZATION: %f ms\n\n" ((end1 -. start1) *. 1000.0);
        let result1 = reduce_to_normal_form_native lambda in 
        print_string (string_of_lambda (result1));
        Printf.printf "\nTime_NATIVE: %f ms\n\n" ((Sys.time() -. end1) *. 1000.0);;


test_reduction l1;;
test_reduction l2;;
test_reduction l3;;
test_reduction l4;;
test_reduction l5;;
test_reduction l6;;
test_reduction l7;;
test_reduction l8;;
test_reduction l9;;

(* Ω combinator is divergent if it has no β-normal form *)
test_reduction omega;; *)                                                                                    