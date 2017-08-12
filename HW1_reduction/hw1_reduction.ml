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

let set_of_list l = 
        List.fold_left (fun set element -> SS.add element set) SS.empty l;;

let dependent_abstractions lambda var = 
        (* Returns a pair of bool - whether var is free at this node of 'lambda'
                                and set -  all abstracted variables, that contain 'var' in their abstraction body *)
        let rec dfs lambda var = 
                match lambda with 
                        | Var x -> if (x = var) then (true, SS.empty) else (false, SS.empty)
                        | Abs(x, p) -> if (x = var) then (false, SS.empty)
                                                              else let (free, set) = dfs p var in 
                                                                     if free then (true, (SS.add x set)) else (false, set) 
                        | App(p, q) -> let (free_p, set_p) = dfs p var in 
                                              let (free_q, set_q) = dfs q var in 
                                              (free_p || free_q, SS.union set_p set_q) in 
        snd (dfs lambda var);;                                                                                              


(* lambda [var := theta] *)
let free_to_subst theta lambda var =
        let free_theta = set_of_list (free_vars theta) in 
        let bound_lambda = dependent_abstractions lambda var in 
        (SS.inter free_theta bound_lambda) = SS.empty;;
        

(* m[x := n] *)
let rec substitute n m x =
    match m with
        | Var y -> if (x = y) then n else m
        | App(p, q) -> App((substitute n p x), (substitute n q x))
        | Abs(y, p) -> if (x <> y) then Abs(y, (substitute n p x)) else m;;

 let rec is_alpha_equivalent l1 l2 = 
    let i = ref 0 in
    let get_fresh_var () = 
        let fresh_var = ("ξ" ^ string_of_int !i) in 
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
                                                                                   