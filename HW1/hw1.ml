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

module CharSet = Set.Make(Char);;

let lambda_of_string x = 
    let rec parse s =
            let symbols = 
                CharSet.of_list ['a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r'; 's';'t';'u';'v';'w';'x';'y';'z';
                                        '0';'1';'2'; '3';'4';'5';'6';'7';'8';'9';'_'] in
            let pos = ref 0 in
            let has_next () = 
                    (!pos < String.length s - 1) in
            let next () = 
                    if has_next() 
                        then pos := (!pos + 1) in
            let rec skip_ws () = 
                    if ((s.[!pos] = ' ') && (has_next())) 
                            then (next (); 
                                     skip_ws()) in
            let curr_symbol () = 
                    skip_ws (); 
                    s.[!pos] in
            let skip x = 
                    if (curr_symbol() <> x )
                        then failwith "unexpected symbol" 
                        else next() in
            let get_var_str () = 
                    let is_valid x = (x = s.[!pos]) in
                    let rec rec_get x = if (CharSet.exists is_valid symbols)
                        then ( x :=  (!x)^(String.make 1 (curr_symbol()));
                                next();
                                rec_get x) 
                        else x in
                    !(rec_get (ref "")) in

            let rec parse_lambda() =
                    let rec get_lambda x = 
                        match x with
                            | '(' -> (skip '(' ; let lambda = parse_lambda() in (skip ')'; lambda))
                            | '\\' -> (skip '\\'; parse_abs())
                            | _ -> parse_var()

                and parse_app l1 = 
                        App(l1, get_lambda (curr_symbol ())) 
                and parse_abs() = 
                            let x = get_var_str() in 
                            skip '.';
                            let l = parse_lambda() in
                            Abs(x, l)        
                and parse_var() = 
                        let x = get_var_str() in 
                        Var(x) in
                let make_lambda x =               
                        let lambda = (get_lambda (x)) in
                        let reflambda = ref lambda in
                        while ( has_next() && (curr_symbol() <> ')')) do
                                reflambda := parse_app (!reflambda);
                        done;
                        !reflambda in
            make_lambda (curr_symbol()) in   
            parse_lambda() in
    parse (x^";");;


let rec string_of_lambda lambda = 
        match lambda with
        | Var x -> x
        | Abs(x, l) -> "(\\" ^ x ^ "." ^ (string_of_lambda l) ^ ")"
        | App(l1, l2) -> "(" ^ (string_of_lambda l1) ^ ") (" ^ (string_of_lambda l2) ^ ")";;
    