open Hw1

module SS = Set.Make(String);;
module StringMap = Map.Make(String);;

let free_vars l = 
    let rec get_fv l bound = 
        match l with
            | Var x -> if (SS.mem x bound) then SS.empty else SS.singleton x
            | App (l1, l2) ->  SS.union (get_fv l1 bound) (get_fv l2 bound)
            | Abs (x, l) -> get_fv l (SS.add x bound) in 
    let fv = get_fv l SS.empty in 
    SS.elements fv;;
        
(*
    1 - place for subst is not found in this subtree
    2 - place is found, and theta is free to subst
    3 - place is found, but theta is not free to subst
*)
let free_to_subst theta lambda var = 
        let fv = SS.of_list (free_vars theta) in 
        let rec dfs p bound_vars =
                let intersects s1 s2 = 
                        not (SS.is_empty (SS.inter s1 s2) ) in 
                let is_var_free x bound_vars = 
                        if (x <> var) then 1 
                        else if (intersects fv bound_vars) then 3 
                        else 2 in 

                let res res1 res2 = 
                    if ((res1 = 2) || (res2 = 2)) then 2 else 
                    if ((res1 = 1) && (res2 = 1)) then 1
                    else 3 in
                
                match p with 
                    | App(p1, q1) -> res (dfs p1 bound_vars) (dfs q1 bound_vars)
                    | Abs (x, p1) -> dfs p1 (SS.add x bound_vars)
                    | Var x ->  is_var_free x bound_vars 
          in  if ((dfs lambda SS.empty) <> 3) then true else false
;;

let rec is_normal_form l = 
        let rec check l = 
                let check_app p q = 
                        match p with 
                                | Abs(x, p1) -> if (free_to_subst q p x) then false else check p1
                                | _ -> (check p) && (check q)
                in match l with
                        | App(p, q) -> check_app p q
                        | Abs(x, p) -> check p
                        | _ -> true
        in check l;;   

 let i = ref 0;;
        let get_fresh_var () = 
            let fresh_var = ("τ" ^ string_of_int !i) in 
            i := !i + 1;
            fresh_var;;

(* m[x := n] *)
let rec substitute n m x =
    match m with
        | Var y -> if (x = y) then n else m
        | App(p, q) -> App((substitute n p x), (substitute n q x))
        | Abs(y, p) -> if (x <> y) then Abs(y, (substitute n p x)) else m;;

let is_alpha_equivalent l1 l2 = 
        let add_new_var var fresh map =
                if (StringMap.mem var map) then map
                                                              else (StringMap.add var fresh map) in 
        let equal x1 map1 x2 map2 = 
                let mapped x mp = 
                        if (StringMap.mem x mp) then (StringMap.find x mp)
                                                                else x in 
                (mapped x1 map1) = (mapped x2 map2) in                                                        

        let rec check l1 map1 l2 map2 = 
                match l1, l2 with
                        | Var x1, Var x2 -> equal x1 map1 x2 map2
                        | App(p1, p2), App(q1, q2) -> (check p1 map1 q1 map2) && (check p2 map1 q2 map2)
                        | Abs(x1, p1), Abs(x2, p2) -> (check p1 (add_new_var x1 ("τ"^x1) map1) p2 (add_new_var x2 ("τ"^x1) map2))
                        | _ -> false in 
        check l1 StringMap.empty l2 StringMap.empty;;

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