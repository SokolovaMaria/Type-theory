open Hw1
open Hw1_reduction
open Hw2_unify

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type

module StringMap = Map.Make(String);;

(* Convertation *)

let rec simp_type_to_algebraic_term simp_type = 
                match simp_type with
                        | S_Elem t -> Hw2_unify.Var (t)
                        | S_Arrow(a, b) -> Hw2_unify.Fun("impl", (simp_type_to_algebraic_term a) :: (simp_type_to_algebraic_term b) :: []);;

let rec algebraic_term_to_simp_type term = 
        match term with 
                | Hw2_unify.Var x -> S_Elem(x)
                | Hw2_unify.Fun(str, head :: tail :: []) -> S_Arrow(algebraic_term_to_simp_type head, algebraic_term_to_simp_type tail) 
                | _ -> failwith("not an algebraic term");;

let infer_simp_type l =

        let i = ref 0 in
        let get_fresh_type () = 
                let fresh_type = ("τ" ^ string_of_int !i) in 
                i := !i + 1;
                fresh_type in
 
        let rec map_type_to_free_vars fv_list map = 
                match fv_list with
                        | [] -> map 
                        | head :: tail -> map_type_to_free_vars tail (StringMap.add head (S_Elem (get_fresh_type()) ) map) in 

(*Recursive function: takes type map as an argument, 
                                  returns system of type equations (system) and type of current lambda (τ)*)
        let rec infer lambda type_map = 
                match lambda with
                        | Hw1.Var x -> ([], StringMap.find x type_map)
                        | Hw1.App(p, q) -> let (sys_p, type_p) = (infer p type_map) in 
                                                     let (sys_q, type_q) = (infer q type_map) in 
                                                     let fresh_type = S_Elem(get_fresh_type ()) in 
                                                     (List.append sys_p (List.append sys_q ((type_p, S_Arrow(type_q, fresh_type) ) :: [] ) ) , fresh_type)
                        | Hw1.Abs(x, p) ->  let type_map1 = StringMap.add x (S_Elem(get_fresh_type())) type_map in
                                                      let (sys_p, type_p) = (infer p type_map1) in 
                                                      (sys_p, S_Arrow(StringMap.find x type_map1, type_p)) in  

        let system, lambda_type = infer l (map_type_to_free_vars (free_vars l) StringMap.empty) in 
        let solution = solve_system (List.map (fun (lhs, rhs) -> 
                                                                        (simp_type_to_algebraic_term lhs, simp_type_to_algebraic_term rhs)) system) in 
        match solution with 
                | Some solution -> Some(List.map (fun (lhs, rhs) -> 
                                                                            (lhs, algebraic_term_to_simp_type rhs)) solution,
                                                                            algebraic_term_to_simp_type (apply_substitution solution (simp_type_to_algebraic_term lambda_type)) )
                | None -> None;;  
                            
(* Hindley-Milner Type Inference. Algorithm W *)

type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

exception TypeInferenceException of string;;
module StringSet = Set.Make(String);;

(* Convertation *)
let rec hm_type_to_algebraic_term hmt = 
        match hmt with
                | HM_Elem t -> Var t
                | HM_Arrow (t1, t2) -> Fun("impl", (hm_type_to_algebraic_term t1) :: (hm_type_to_algebraic_term t2) :: [])
                | HM_ForAll (a, t) -> raise (TypeInferenceException "all types should have been already instantiated");; 

let rec algebraic_term_to_hm_type term = 
        match term with 
                | Var t -> HM_Elem t
                | Fun("impl", t1 :: t2 :: []) -> HM_Arrow(algebraic_term_to_hm_type t1, algebraic_term_to_hm_type t2)
                | _ -> failwith "now pattern-matching is exhaustive";;       

let algorithm_w lambda =   

        let i = ref 0 in
        let get_fresh_type () =
                let fresh_type = ("β" ^ string_of_int !i) in 
                i := !i + 1;
                fresh_type in

        let j = ref 0 in
        let initial_environment_vars () =
                let fresh_type = ("φ" ^ string_of_int !j) in 
                j := !j + 1;
                fresh_type in        

        (* Applies substitution, defined with 'subst_map' to hm_type *)
        let substitute subst_map hmt = 
                let rec subst hmt bound_types_set =
                        match hmt with
                                | HM_Elem (t) -> if (StringSet.mem t bound_types_set) 
                                                                then hmt
                                                                else if (StringMap.mem t subst_map) 
                                                                                then (StringMap.find t subst_map)
                                                                                else hmt
                                | HM_Arrow (t1, t2) -> HM_Arrow ((subst t1 bound_types_set), (subst t2 bound_types_set))
                                | HM_ForAll (a, t) -> HM_ForAll (a, (subst t (StringSet.add a bound_types_set))) in 
                 subst hmt StringSet.empty in                                                                 

        (* Removes surface ∀ quantifiers and substitutes fresh type variables instead of bound ones *)
        let rec instantiate_type hmt = 
                match hmt with
                        | HM_ForAll (a, hmt1) -> substitute (StringMap.singleton a (HM_Elem(get_fresh_type ()))) (instantiate_type hmt1)
                        | _ -> hmt in 

        let substitute_into_environment subst_map env = 
                StringMap.fold (fun x x_type env' -> StringMap.add x (substitute subst_map x_type) env') env StringMap.empty in    

        (* Converts substitution, returned by Robinson's unification algorithm as a list, to substitution map *)
        let subst_list_to_map subst_list = 
                List.fold_left (fun map (x, term) -> (StringMap.add x (algebraic_term_to_hm_type term) map)) StringMap.empty subst_list in                                            

         let compose s2 s1 = 
                let s2_applied_to_s1 = StringMap.fold (fun x x_type map -> StringMap.add x (substitute s2 x_type) map) s1 StringMap.empty in         
                StringMap.fold (fun x x_type map -> if (StringMap.mem x map) then map else (StringMap.add x x_type map)) s2 s2_applied_to_s1 in

         let free_type_vars_hm_type t =
                let rec ftv t bound_tv =
                        match t with 
                                | HM_Elem t -> if (StringSet.mem t bound_tv) then StringSet.empty else StringSet.singleton t 
                                | HM_Arrow(t1, t2) -> StringSet.union (ftv t1 bound_tv) (ftv t2 bound_tv)
                                | HM_ForAll (a, t) -> ftv t (StringSet.add a bound_tv) in 
                ftv t StringSet.empty in                 

          let free_type_vars_environment env = 
                StringMap.fold (fun x x_type set -> StringSet.union (free_type_vars_hm_type x_type) set) env StringSet.empty in 

         (*Abstracts a type over all type variables which are free in the type but not free in the given type environment *) 
         let generalize env t = 
                let free_tv_type = free_type_vars_hm_type t in
                let free_tv_env = free_type_vars_environment env in 
                let type_not_env = StringSet.diff free_tv_type free_tv_env in 
                StringSet.fold (fun a generalized_type -> HM_ForAll(a, generalized_type)) type_not_env t in   

        let rec free_vars_hm_lambda hml =
                let rec fv hml bound = 
                        match hml with 
                                | HM_Var x -> if (StringSet.mem x bound) then StringSet.empty else StringSet.singleton x 
                                | HM_Abs (x, e) -> fv e (StringSet.add x bound)
                                | HM_App (e1, e2) -> StringSet.union (fv e1 bound) (fv e2 bound)
                                | HM_Let (x, e1, e2) -> StringSet.union (fv e1 bound) (fv e2 (StringSet.add x bound)) in 
                fv hml StringSet.empty in                 

        let get_type_environment hml = 
                let fv_set = free_vars_hm_lambda hml in 
                StringSet.fold (fun x map -> StringMap.add x (HM_Elem(initial_environment_vars())) map) fv_set StringMap.empty in 

        (* W is a function from a type environment and a term
                                   to a pair of a substitution S and a type τ *)
        let rec w env lambda =
                match lambda with
                        | HM_Var (x) -> if (StringMap.mem x env) then (StringMap.empty, instantiate_type (StringMap.find x env))
                                                                                       else raise (TypeInferenceException ("unbound variable: " ^ x))

                        | HM_Abs(x, e) ->  (let fresh_type = HM_Elem(get_fresh_type()) in 
                                                    let env' = StringMap.remove x env in 
                                                    let env'' = StringMap.add x fresh_type env' in 
                                                    let s1, t1 = w env'' e in 
                                                   (s1, HM_Arrow((substitute s1 fresh_type), t1)))

                        | HM_App(e1, e2) ->  (let fresh_type = HM_Elem(get_fresh_type()) in 
                                                        let s1, t1 = w env e1 in 
                                                        let s2, t2 = w (substitute_into_environment s1 env) e2 in 
                                                        let subst_list = solve_system([(hm_type_to_algebraic_term (substitute s2 t1)), (hm_type_to_algebraic_term(HM_Arrow(t2, fresh_type)))]) in 
                                                        match subst_list with
                                                                | None -> raise (TypeInferenceException "Unification algorithm failed to get substitution")
                                                                | Some subst_list -> let s3 = subst_list_to_map subst_list in 
                                                                                                (compose s3 (compose s2 s1), substitute s3 fresh_type))

                        | HM_Let (x, e1, e2) -> (let s1, t1 = w env e1 in 
                                                           let env' = StringMap.remove x env in 
                                                           let t' = generalize (substitute_into_environment s1 env) t1 in 
                                                           let env'' = StringMap.add x t' env' in 
                                                           let s2, t2 = w (substitute_into_environment s1 env'') e2 in 
                                                           (compose s2 s1, t2)) in 
        let env = get_type_environment lambda in
        try 
                let subst_map, hm_lambda_type = w env lambda in 
                Some ((StringMap.bindings subst_map), hm_lambda_type)
        with (TypeInferenceException error) ->
                print_string (error ^ "\n");
                None;;     
