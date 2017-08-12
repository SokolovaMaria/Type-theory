type peano = Z | S of peano;; 
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int (n:int):peano =
    match n with
        | 0 -> Z
        | nn -> S(peano_of_int(n - 1));;

let rec int_of_peano (n:peano):int =
    match n with
        | Z -> 0
        | S(nn)-> (1 + int_of_peano nn);;   

let rec add x y =  
    match y with
        | Z -> x
        | S yy -> S (add x yy);;

let inc (x) = add x (S Z);;      

let rec sub x y = 
    match (x, y) with
        | (x, Z) -> x
        | (Z, y) -> Z
        | (S xx, S yy) -> (sub xx yy);;


let rec mul x y  =
    match y with
        | Z -> Z
        | S yy -> add (mul x yy) x;;

let greater x y = if (sub x y) = Z then y else x;;        

let rec div x y =
    if y = Z then failwith "Division by zero!!!" 
    else if (greater x y) = y then Z 
    else (add (S Z) (div (sub x y) y));;       
 
 
let rec power x y =
    match y with 
        | Z -> (S Z)
        | S yy -> mul (power x yy) x;;
        
                     

let rec reverse (list, rlist) = 
    match list with
        | [] -> rlist
        | head::tail -> reverse (tail, head::rlist);;

let rev x = reverse (x, []);;



let rec split = function
    | [] 
    | [_] as t1 -> t1, []
    | h::t ->
        let t1, t2 = split t in
          h::t2, t1;;

let rec merge = function
    | list, []
    | [], list -> list
    | ha::ta, hb::tb ->
        if ha <= hb then ha :: merge (ta, hb::tb)
                            else hb :: merge (ha::ta, tb);;

  let rec merge_sort = function
    | [_] as list -> list
    | list ->
        let left, right = split list in
            merge (merge_sort left, merge_sort right);;

                     
let lambda_of_string str = 
        let rec parse_string s =
                let pos = ref 0 in
                let has_next () = if ( !pos < String.length s - 1 ) then true else false in
                let next_pos () = if ( has_next () ) then pos := ( !pos + 1 ) in
                let rec skip_ws () = if ( (has_next () ) && ( s.[!pos] = ' ' )) then ( next_pos (); skip_ws () ) in
                let curr_symbol () = (skip_ws (); s.[!pos]) in
                let skip_symbol x = if (x = curr_symbol ()) then next_pos () else failwith "unexpected symbol" in 
                let is_valid x = if ((x >= '0' && x <= '9') || (x >= 'a' && x <= 'z')) then true else false in
                let get_var_str () = 
                        let rec get var = 
                                if ( is_valid (curr_symbol ()) ) 
                                then (
                                        var := (!var) ^ (String.make 1 (curr_symbol ()));
                                        next_pos ();
                                        get (var)                                                                                                                                                                                                                                                                                                                                                                                                                           
                                ) else var in 
                        !(get (ref "")) in
                 let rec parse_lambda () =
                        let rec parse () =  
                            match curr_symbol () with
                                | '\\' -> ( skip_symbol '\\'; parse_abs () )
                                | '(' -> ( skip_symbol '('; let lambda = parse_lambda () in skip_symbol ')'; lambda )
                                | _ ->  parse_var()  

                        and parse_var () = let var = get_var_str () in Var(var) 
                        and parse_abs () = (let var = get_var_str () in skip_symbol '.'; let lambda = parse () in Abs (var, lambda)) 
                        and parse_app left = App( left, parse () ) 
                        and get_lambda () = 
                                let lambda = ref (parse ()) in 
                                while (has_next() && curr_symbol () <> ')') do 
                                        lambda := parse_app (!lambda);
                                done;
                                !lambda in 
                        get_lambda () in 
                parse_lambda() in 
        parse_string (str ^ ";");;

let rec string_of_lambda lambda = 
        match lambda with
        | Var x -> x
        | Abs(x, l) -> "(\\" ^ x ^ "." ^ (string_of_lambda l) ^ ")"
        | App(l1, l2) -> "(" ^ (string_of_lambda l1) ^ ") (" ^ (string_of_lambda l2) ^ ")";;
    