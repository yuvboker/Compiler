
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec compare_lists l1 l2 = 
	match l1,l2 with
  | [],[] -> true
  | (_::_),[] -> false
  | [], (_::_) -> false
  | (car1::cdr1),(car2::cdr2) -> if (sexpr_eq car1 car2) then (compare_lists cdr1 cdr2) else false

and sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> compare_lists l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

open PC;;
let make_enclosed _l_ _p_ _r_ =
        let _enclosed_ = caten (caten _l_ _p_) _r_ in
        pack _enclosed_ (fun ((l, p), r) -> p);;



 
(* Tokens *)

(* Helpers *)
let left_p = char '(';;
let right_p = char ')';;
let left_b = char '[';;
let right_b = char ']';;
(* Whitespaces - any ASCII char <= 32 is considered a whitespace *)
let space = pack (range '\000' ' ')(fun (_) -> []);;
let nt_end_of_line = disj_list[(word "\n") ;(word_ci "#\\newline"); (word_ci "#\\xa")];;
let nt_end_of_comment = disj nt_end_of_line nt_end_of_input;;
let nt_semicolon = char ';';;
let letters = pack(range_ci 'a' 'z')(fun(e)-> (lowercase_ascii e));;
let punc = one_of "!$^*-_=<>/?+:";;
let comment_sign = word "#;" ;;            
let prefix = word "#\\";;
let ranged_visible_chars = range '!' '\127';;
let digit = range '0' '9';;
let hex_digit =
  let big =  range_ci 'a' 'f' in
  disj digit big;;
let digits = plus digit;;
let hex_digits = plus hex_digit;;
let pos = char '+';;
let neg = char '-';;
let sign = pack (disj pos neg)(fun (ch) -> [ch]);;
let hex  = word_ci "#x";;
let sign_appearance =  disj sign nt_epsilon;;
let decimal_point = pack (char '.') (fun (_) -> ['.']);;
let nt_right_paren s =
      let (_, _) = (char ')' ) s  in
      ([],s) ;;
let nt_right_paren2 s =
      let (_, s1) = (char ')' ) s  in
      ([],s1) ;;
let nt_right_bracket2 s =
      let (_, s1) = (char ']' ) s  in
      ([],s1) ;;
let nt_right_bracket s =
      let (_, _) = (char ']' ) s  in
      ([],s) ;;
let nt_left_paren s =
      let (_, _) = (char '(' ) s  in
      ([],s) ;;
let nt_left_bracket s =
      let (_, _) = (char '[' ) s  in
      ([],s) ;;
let nt_quote s =
      let (_, _) = (char '\"' ) s  in
      ([],s) ;;
let nt_hash s =
      let (_, _) = (char '#' ) s  in
      ([],s) ;;
let nt_quoted s =
      let (_, _) = (word "'" ) s  in
      ([],s) ;;
let nt_digit s =
      let (_, _) = digit  s  in
      ([],s) ;;
let nt_sign s =
      let (_, _) = sign  s  in
      ([],s) ;;
let nt_quasi s =
      let (_, _) = (word "`" ) s  in
      ([],s) ;;
let nt_comma s =
      let (_, _) = (word "," ) s  in
      ([],s) ;;
let dots s =
      let (_, _) = (word "..." ) s  in
      ([],s) ;;
let complement_bracket s =
      let (_, _) = (word "..." ) s in
      (']',s);;
let complement_paren s =
      let (_, _) = (word "..." ) s in
      (')',s);;




(* Bool *)
let nt_true =
  let bool_true = word_ci "#T" in
  pack (bool_true)(fun (_) -> Bool true);;

let nt_false =
  let bool_false = word_ci "#F" in
  pack (bool_false)(fun (_) -> Bool false);;

let _bool_ = disj nt_true nt_false;;



(* Number *)

                                            
let rec _number_ s =
  disj scientific (disj float_sexp int_sexp) s
            
and decimal_int s = pack (caten sign_appearance digits)
                         (fun (sign, digits) -> match sign with  
                                               |['-'] -> Int (0 - int_of_string (list_to_string digits))                                    
                                               | sign -> Int (int_of_string (list_to_string digits))) s 
                         
and hex_int s = pack (caten_list [hex ; sign_appearance ; hex_digits])
                    (fun (float ) -> match float with
                                     |  [ _ ; ['-'] ; digits] -> Int (int_of_string (list_to_string (List.append (string_to_list "-0x")  digits)))
                                     |  [ _ ; _ ; digits] ->  Int (int_of_string (list_to_string (List.append (string_to_list "0x")  digits)))
                                     | float -> raise X_no_match) s
                    
and decimal_float s = pack (caten_list [sign_appearance ; digits ; decimal_point ; digits])
                          (fun ( float ) -> match float with
                                               | [ ['-'] ; digits1 ; _ ; digits2] -> Float (0. -. float_of_string (list_to_string (List.concat [ digits1; ['.']; digits2] )))
                                               | [ _ ; digits1 ; _ ; digits2] -> Float (float_of_string (list_to_string (List.concat [ digits1 ; ['.'] ; digits2])))          
                                               | float -> raise X_no_match) s
 
             

and hex_float s = pack (caten_list [hex ; sign_appearance ; hex_digits ; decimal_point ; hex_digits])
                          (fun (float) -> match float with
                                               | [ _ ; ['-']; digits1 ; _ ; digits2] -> Float (0. -. float_of_string (list_to_string (List.concat [(string_to_list "0x") ; digits1; ['.'] ; digits2])))
                                               | [ _ ; _ ; digits1 ; _ ; digits2] -> Float (float_of_string (list_to_string (List.concat [(string_to_list "0x"); digits1; ['.'];  digits2])))        
                                               | float ->  raise X_no_match) s             
and int s = (disj hex_int decimal_int) s                
and int_sexp s = (pack int (fun (x) -> Number(x))) s
and float s = (disj hex_float decimal_float) s                 
and float_sexp s= (pack float (fun (x) -> Number(x))) s                                                                  
and scientific s = (pack (caten (disj float int) (caten (char_ci 'e')  int)) (fun(sci) -> match sci with
                                                                                  |(Int(l),(_, Int(r))) ->
                                                                                    Number (Float(float_of_string (String.concat ""  [(string_of_int l) ; "e" ;(string_of_int r)])))
                                                                                  |(Float(l),(_, Int(r))) ->
                                                                                    Number (Float(float_of_string (String.concat ""  [(string_of_float l) ; "e" ;(string_of_int r)])))
                                                                                  |sci -> raise X_no_match )) s
                                                                             


(* Symbol *)


let _symbol_ =
  let options = plus (disj_list [digit ; letters ; punc]) in
  pack options (fun (s)-> Symbol((list_to_string s)));;


(* String *)




let _str_ =
  let xa = pack(word_ci "\\xa;")(fun(w)-> '\x0a') in
  let x9 = pack(word_ci "\\x9;")(fun(w)-> '\x09') in
  let xc = pack(word_ci "\\xc;")(fun(w)-> '\x0c') in
  let xd = pack(word_ci "\\xd;")(fun(w)-> '\x0d') in
  let x5c = pack(word_ci "\\x5c;")(fun(w)-> '\x5c') in
  let x22 = pack(word_ci "\\x22;")(fun(w)-> '\x22') in
  let newline = pack(word_ci "\\n")(fun(w)-> '\n') in
  let return = pack(word_ci "\\r")(fun(w)-> '\r') in
  let tab  = pack(word_ci "\\t")(fun(w)-> '\t') in
  let page = pack(word_ci "\\f")(fun(w)-> '\x0c') in
  let backslash  = pack(word_ci "\\\\")(fun(w)-> '\\') in
  let double_quote = pack(word_ci "\\\"")(fun(w)-> '\"') in
  
  let meta = disj_list [xa; x9; xc; xd;x5c;x22;newline;return;tab;page;backslash;double_quote] in
  
  let hex = pack ( caten (word_ci "\\x") (caten hex_digits (char ';')))
                 (fun (prefix, (digits,es) ) -> match prefix with
                                                  | (car :: cdr) -> (list_to_string (List.append ['0';'x'] digits))
                                                  | _ -> raise X_no_match) in
  
  let not_meta =  pack hex (fun (str) ->  if (str < "0x21") then ' '
                                         else (char_of_int (int_of_string str))) in
  let hex_string = disj meta not_meta in
  let quote = char '\"' in
  let str_diff_quote = diff nt_any quote in
  pack (caten quote (caten (star (disj hex_string str_diff_quote)) quote))
               (fun (l, (exp, r)) -> String (list_to_string exp));;

(* Char *)

let named_chars =
  let nul = pack (word_ci "#\\nul") (fun (w) -> Char('\000')) in
  let newline = pack (word_ci "#\\newline") (fun (w) -> Char('\n')) in
  let return = pack (word_ci "#\\return")
                 (fun (w) -> Char('\r')) in
  let tab = pack (word_ci "#\\tab") (fun (w) -> Char('\t')) in
  let formfeed = pack (word_ci "#\\page") (fun (w) -> Char('\012')) in
  let space = pack (word_ci "#\\space") (fun (w) -> Char(' ')) in
  disj_list [nul; newline ; return ; tab ; formfeed ; space ] ;;


let visible_chars = pack (caten prefix ranged_visible_chars)
                         (fun (_,es) -> Char (es) );;
let hex_char =                    
  let xa = pack(word_ci "#\\xa")(fun(w)-> '\x0a') in
  let x9 = pack(word_ci "#\\x9")(fun(w)-> '\x09') in
  let xc = pack(word_ci "#\\xc")(fun(w)-> '\x0c') in
  let xd = pack(word_ci "#\\xd")(fun(w)-> '\x0d') in
  let x0 = pack(word_ci "#\\x0")(fun(w)-> '\x00') in
  let meta = disj_list [xa; x9; xc; xd; x0] in
  let hex = pack ( caten (word_ci "#\\x") hex_digits)
                 (fun (_ , digits ) -> (list_to_string (List.append ['0';'x'] digits))) in
                                                
  
  let not_meta =  pack hex (fun (str) ->  if (str < "0x21") then ' '
                                         else (char_of_int (int_of_string str))) in
  let ans = disj meta not_meta in
  pack ans (fun (ch) -> Char(ch)) ;;

let _char_ = disj_list [hex_char; named_chars; visible_chars] ;;

let rec sexp s =
  let first_step = disj_list [prim; compound ;quotes]  in
  let second_step = caten garbage_s first_step  in
  let third_step = pack second_step (fun(l,e)-> e) in
  third_step s
             
and sexp_comp s =
  let first_step = disj_list [prim; compound_comp ;quotes]  in
  let second_step = caten garbage_s first_step  in
  let third_step = pack second_step (fun(l,e)-> e) in
  third_step s
             
and prim s =
  disj_list [sexpr_bool; sexpr_char;sexpr_number;sexpr_string;sexpr_symbol; sexpr_nil] s
            
and sexpr_bool s =
  pack (caten _bool_ validation)(fun(e,es)->e) s
                                             
and sexpr_number s =
  pack (caten _number_ validation)(fun(e,es)->e) s
        
and sexpr_char s =
  pack (caten _char_ validation)(fun(e,er)-> e) s                                            
      
and sexpr_string s =
  pack (caten _str_  validation)(fun(e,es)-> e) s
       
and sexpr_symbol s =  
  pack (caten _symbol_ validation)(fun(e,es)-> e) s

and erase_three_points s =
  let erase = pack (word "...")(fun(e)->[]) in
  pack (caten (disj erase nt_epsilon) garbage_s) (fun(e,es)-> e) s
  
and three_dots_paren s =
  let clean = pack (caten right_p garbage_s)(fun(e,es)->e) in
  (disj clean complement_paren) s

  
and three_dots_bracket s =
  let clean = pack (caten right_b garbage_s)(fun(e,es)->e) in
  (disj clean complement_bracket) s        
    
and sexpr_nil s =
  let nil = make_enclosed left_p garbage_s three_dots_paren in
  let brackets = make_enclosed left_b garbage_s three_dots_bracket in
  let choose = disj brackets nil in
  (pack choose (fun (es) -> Nil)) s

and compound s =
  (disj pair vector) s

and compound_comp s =
   (disj pair_comp vector) s                     
                     
and pair s =
  let erase_dots = pack(word "...")(fun(e)->[]) in
  let nested_b_comp = make_enclosed left_b cons_b_comp erase_dots in
  let nested_p_comp = make_enclosed left_p cons_p_comp erase_dots in
  let nested_b = pack(caten left_p cons_p)(fun(e,es)->es) in
  let nested_p = pack(caten left_b cons_b)(fun(e,es)->es) in
  (disj_list [nested_p_comp ; nested_b_comp; nested_b; nested_p]) s

and pair_comp s =
  let nested_b_comp = make_enclosed left_b cons_b_comp garbage_s in
  let nested_p_comp = make_enclosed left_p cons_p_comp garbage_s in
  let nested_b = pack(caten left_p cons_p)(fun(e,es)->es) in
  let nested_p = pack(caten left_b cons_b)(fun(e,es)->es) in
  (disj_list [nested_p_comp ; nested_b_comp; nested_b; nested_p]) s
                                                                  
and vector s =
  (pack (caten (char '#') list_vector)(fun (e,er) -> er)) s 

and list_pair_b_comp s =
  let is_dotted = make_enclosed decimal_point sexp_comp (caten garbage_s (disj nt_right_bracket2 nt_epsilon))  in
  let is_end = pack three_dots_bracket (fun(e)->Nil) in
  (disj_list [is_dotted ;is_end; cons_b_comp]) s
                                          
and list_pair_p_comp s =
  let is_dotted = make_enclosed decimal_point sexp_comp (caten garbage_s (disj nt_right_paren2 nt_epsilon))  in
  let is_end = pack three_dots_paren (fun(e)->Nil) in
  (disj_list [is_dotted ; is_end ; cons_p_comp]) s                     

and cons_b_comp s =
  pack (caten sexp_comp list_pair_b_comp)(fun(e,es)->Pair(e,es)) s

and cons_p_comp s =
  pack (caten sexp_comp list_pair_p_comp)(fun(e,es)->Pair(e,es)) s 
                                                          
and list_pair_b s =
  let clean = pack (caten right_b garbage_s)(fun(e,es)->e) in
  let is_dotted = make_enclosed decimal_point sexp three_dots_bracket in
  let is_end = pack clean (fun(e)->Nil) in
  (disj_list [is_dotted ;is_end; cons_b]) s

and list_pair_p s =
  let clean = pack (caten right_p garbage_s)(fun(e,es)->e) in
  let is_dotted = make_enclosed decimal_point sexp three_dots_paren in
  let is_end = pack clean (fun(e)->Nil) in
  (disj_list [is_dotted ; is_end ; cons_p]) s                     

and cons_b s =
  pack (caten sexp list_pair_b)(fun(e,es)->Pair(e,es)) s

and cons_p s =
  pack (caten sexp list_pair_p)(fun(e,es)->Pair(e,es)) s             
       
and list_vector s =
  let go_on =  star sexp  in
  let list_sexp = pack (caten (caten left_p garbage_s) (caten go_on three_dots_paren))
                    (fun (l, (e,r)) -> Vector(e)) in
   list_sexp s           
                                     
and quotes s =
  let quoted = pack (word "'") (fun (_) -> '1') in
  let qquoted = pack (word "`") (fun (_) -> '2') in
  let unquoted_spliced = pack (word ",@")(fun(_)-> '3') in
  let unquoted = pack (word ",")(fun(_)-> '4') in
  let sign = disj_list [quoted; qquoted; unquoted_spliced ; unquoted] in
  let enclosed = (pack (caten sign sexp)
        (fun (sign, sexpr)->match sign with
                                  |'1' -> Pair(Symbol("quote"), Pair(sexpr,Nil))
                                  |'2' -> Pair(Symbol("quasiquote"), Pair(sexpr,Nil))
                                  |'3' -> Pair(Symbol("unquote-splicing"), Pair(sexpr,Nil)) 
                                  |'4' -> Pair(Symbol("unquote"), Pair(sexpr,Nil))
                                  | sign -> raise X_no_match)) in
  enclosed s

and validation s =
  (disj_list [nt_comma;nt_hash;nt_quoted;nt_quasi;nt_digit;nt_sign; dots ; nt_quote ; nt_left_bracket; nt_left_paren ; nt_right_bracket; nt_right_paren ; nt_end_of_input ; garbage_p]) s       

and garbage_s s =
  (star (disj_list [space ;line_comment ;sexpr_comment])) s

and garbage_p s =
  (plus (disj_list [space ;sexpr_comment ;line_comment])) s
                                                          
and sexpr_comment s =
  let go_on = caten comment_sign no_sexpr_comment in
  (pack (caten go_on loop) (fun(_)->[])) s
                             
and loop s =
   (caten comment sexp) s
                                    
and no_sexpr_comment s =
  star (disj_list [space;line_comment]) s
                                    
and comment s =
  let go_on = caten comment_sign no_sexpr_comment in
  let comb = pack (caten go_on loop)(fun(_)->[]) in
  (disj comb nt_epsilon)  s

and line_comment s =
  let nt_any_except_newline = diff nt_any nt_end_of_comment in
  let no_newline = star nt_any_except_newline in
  let until_end_of_comment = pack (caten no_newline  nt_end_of_comment)
                                  (fun (e, es) ->[] ) in
  (pack (caten nt_semicolon until_end_of_comment)
       (fun (e, es) -> [])) s;;


let rem_dots = pack (word "...")(fun (_) -> []);;
let garbage_dots s =
  (star (disj_list [rem_dots;space ;line_comment ;sexpr_comment])) s;;

let just_one_sexp =
  let check = pack(make_enclosed garbage_dots sexp garbage_dots)(fun(e)->e) in
  pack (caten check nt_end_of_input)(fun(e,er)->e);;




let rec sexps s=
  (disj nt_end_of_input loop2) s

and loop2 s =
  let check = pack (make_enclosed garbage_dots sexp garbage_dots)(fun(e)->[e]) in
  pack(caten check sexps)(fun(e,es)-> List.append e es)  s;;

let read_sexpr string =
  let (a,b) = test_string just_one_sexp string in
  a;;

let read_sexprs string =
  let (a,b) = test_string sexps string in
  a;;
  
end;; (* struct Reader *)
