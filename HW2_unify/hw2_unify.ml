type algebraic_term = Var of string | Fun of string * (algebraic_term list)

module CountMap = Map.Make(String);;

let system_to_equation x = failwith "Not implemented";;

(*Robinson's algorithm*)
let solve_system system = 

        let make_transformed_system_option system = 
                let append_equations tail current = 
                        match tail with 
                                | None -> None
                                | Some tail -> match current with 
                                                            | None -> None
                                                            | Some current -> Some (List.append current tail) in 
                List.fold_left append_equations (Some ([])) system in                                               

        let rec transform_system equation =

                let term_contains_var term var = 
                        let rec contains t = 
                                match t with 
                                        | Var (x) -> (x = var)
                                        | Fun (f, args) -> List.mem true (List.map contains args) in 
                        contains term in 

                match equation with
                        (*{f (a1 , . . . an ) = g(b1 , . . . bn )} : if (f = g) then {a1 = b1;...an = bn} else system is unsolvable*)
                        | Fun (f, args1), Fun(g, args2) -> if ((f = g) && (List.length args1 = List.length args2)) 
                                                                              then
                                                                                        let new_equations = List.combine args1 args2 in 
                                                                                        make_transformed_system_option (List.map transform_system new_equations)
                                                                              else 
                                                                                        None 
                         (* {x = T} : if (T contains x) then system is unsolvable else {x = T}    *)                                                            
                         | Var (x), Fun (f, args) | Fun (f, args), Var (x) -> if (term_contains_var (Fun(f, args)) x)
                                                                                                       then 
                                                                                                                None
                                                                                                       else   
                                                                                                                Some((Var(x), Fun(f, args)) :: [])                                                                          
                         (*{x = y} : if (x = y) then throw away this equation else {x = y}*)
                         | Var(x), Var(y) -> if (x = y) 
                                                        then 
                                                                Some( [] )
                                                        else 
                                                                Some((Var(x), Var(y)) :: []) in 

                                                           
        (*{x = T; S = R...} : if (S or R contains x) then {x = T; S[x := T]; R[x := T]...}*)
        (*T won't contain x - 'transform_system' will take care of that*)                                                            
        let rec make_substitutions system =

                (*counts the number of occurences in terms of all variables*)
                let count_var_occurences_in_system sys = 
                       let rec count_var_occurences_in_terms terms_list count_map = 
                                List.fold_left (fun map term ->
                                                            match term with
                                                                    | Var (x) -> (let count = ref (if (CountMap.mem x map) then (CountMap.find x map) else 0) in 
                                                                                        count := !count + 1;
                                                                                        CountMap.add x !count map)
                                                                    | Fun (f, args) -> count_var_occurences_in_terms args map) count_map terms_list in 
                        let lhs, rhs = List.split sys in 
                        let count_map = count_var_occurences_in_terms lhs CountMap.empty in 
                        count_var_occurences_in_terms rhs count_map in 

                (*substitutes given term into all terms of the list instead of x if possible*)      
                let rec substitute_term term term_list x = 
                        List.map (fun list_element -> match list_element with
                                                                                | Var (y) -> if (y = x) then term else Var (y)
                                                                                | Fun (f, args) -> Fun (f, (substitute_term term args x)) ) term_list in 

                let var_occurences_map = count_var_occurences_in_system system in 

                (*finds the first equation in the system with rhs ready for substitution*)
                (*TODO: think of the way to avoid iteration through the whole system*)
                let find_first_and_carry sys = 
                        List.fold_left (fun first_equation_with_term_for_substitution current_equation -> 
                                              match first_equation_with_term_for_substitution with 
                                                        | Some (already_found) -> Some (already_found) (*just carry it through*)
                                                        | None -> (match current_equation with
                                                                                | Var(x), term -> if ((CountMap.find x var_occurences_map) > 1) 
                                                                                            then Some(x, term)
                                                                                            else None
                                                                                | _, _ -> None) ) None system in 

                let first_equation_with_term_for_substitution = find_first_and_carry system in

                match first_equation_with_term_for_substitution with 
                        | Some(x, term) -> let lhs, rhs = List.split system in 
                                                        let lhs1 = substitute_term term lhs x in 
                                                        let rhs1 = substitute_term term rhs x in 
                                                        let new_equations = List.combine lhs1 rhs1 in 
                                                        let system1 = make_transformed_system_option (List.map transform_system new_equations) in 
                                                        (match system1 with
                                                                (*add {x = T}*) 
                                                                | Some sys -> make_substitutions ((Var(x), term) :: sys)
                                                                | None -> None )
                         (*nothing to substitute -> just add all equations to system*)                                           
                         | None -> Some (List.map (fun equation -> match equation with
                                                                                                        | Var(x), term -> (x, term)
                                                                                                        | _, _ -> failwith "some trouble") system ) in 
    
               let transformed_system = make_transformed_system_option (List.map transform_system system) in 
               match transformed_system with 
                        | Some transformed_system -> make_substitutions transformed_system
                        | None -> None;;
                                                                                                                                                                                                                                                                                                                                                                                                                                   
let check_solution solution initial_system = 
        let vars, terms = List.split solution in 
        let solution_var_map = List.fold_left (fun map var -> 
                                                                    CountMap.add var (List.assoc var solution) map) CountMap.empty vars in
        let lhs_init, rhs_init = List.split initial_system in 
        let rec substitute_solution terms = 
                List.map (fun term -> 
                                    match term with
                                            | Var x -> if (CountMap.mem x solution_var_map) 
                                                                then (CountMap.find x solution_var_map)
                                                                else Var(x)
                                            | Fun(f, args) -> Fun(f, (substitute_solution args))) terms in 
        let lhs_init1 = substitute_solution lhs_init in 
        let rhs_init1 = substitute_solution rhs_init in 
        lhs_init1 = rhs_init1;;

let apply_substitution solution term = 
        let rec map_of_solution solution map = 
                match solution with 
                        | [] -> map
                        | (lhs, rhs) :: tail -> map_of_solution tail (CountMap.add lhs rhs map) in 
        let map = map_of_solution solution CountMap.empty in 
        
        let rec subst term = 
                match term with 
                        | Var(x) -> if (CountMap.mem x map) then (CountMap.find x map) else Var(x)
                        | Fun(f, args) -> Fun(f, (List.map subst args)) in 
                subst term;;              


                                                                                                                                
                    