#use "semantic-analyser.ml";;

 
module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> sob list
  val make_fvars_tbl : expr' list -> free_var_pair list
  val generate : sob list -> free_var_pair list -> expr' -> string
end;;


module Code_Gen : CODE_GEN = struct
(* let generate consts fvars e = raise X_syntax_error;;
 let generate_print consts fvars e = raise X_syntax_error;;
 let make_consts_tbl exprs = raise X_syntax_error;;
 let make_fvars_tbl exprs = raise X_syntax_error;;
end;; *)
 
let run exp =
 List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs exp));;
                                                                                                  
let rec run_on_all exprs =
  match exprs with
  |(car :: cdr)-> List.cons (run car)
                    (run_on_all cdr)
  |exprs -> [];;

let sob_exists exp table =
  List.exists (fun(ConstSOB(y,_,_))-> (expr'_eq exp (Const'(y)))) table;;

let rec sob_offset exp table =
  let ans = (List.filter (fun(ConstSOB(y,_,_))-> (expr'_eq exp (Const'(y)))) table) in
  match ans with
  |[] -> -1
  |[ConstSOB(_,offset,_)] -> offset
  |ans -> raise X_syntax_error;;

let rec last_offset table =
  match table with
  |(ConstSOB(Sexpr(x),offset,_) :: [])-> (match x with
                                         |Number(_)->offset + 9
                                         |Char(_)->offset + 2
                                         |String(x)-> let length = String.length x in
                                                      offset + 9 + length
                                         |Symbol(_)-> offset + 9
                                         |Pair(_,_) -> offset + 17
                                         |Vector(x) -> let length =   List.length x in
                                                       offset + 9 + (length*8)
                                         |x-> 6)
  |(car :: cdr) -> last_offset cdr
  |table -> 0;;
                              
let string_to_chars s =
  let rec loop i length =
    if i < 0 then length else loop (i - 1) (s.[i] :: length) in
  loop (String.length s - 1) [];;

let string_of_int list=
	String.concat "," (List.map (fun(x)-> string_of_int (int_of_char x)) list);;

let convert_string s = 
	let chars_list = string_to_chars s in
	string_of_int chars_list;;

 


let rec make_const_tbl exp offset table =
  match exp with
  |(car :: cdr)-> let bool = sob_exists car table in
                        if bool then (make_const_tbl cdr offset table) else
                          (match car with
                           |(Const'(Sexpr(Number(Int(x)))))->
                             let sob = (ConstSOB(Sexpr(Number(Int(x))),offset,
                                                 (Printf.sprintf "MAKE_LITERAL_INT(%d)" x))) in
                             let table = (List.append table [sob]) in
                              (make_const_tbl cdr (offset+9) table)
                           |(Const'(Sexpr(Number(Float(x)))))->
                             let sob = (ConstSOB(Sexpr(Number(Float(x))),offset,
                                                 (Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" x))) in
                             let table = (List.append table [sob]) in
                             (make_const_tbl cdr (offset+9) table)
                           |(Const'(Sexpr(Char(x))))->
                             let sob = (ConstSOB(Sexpr(Char(x)),offset,
                                                 (Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (int_of_char x)))) in
                             let table = (List.append table [sob]) in
                             (make_const_tbl cdr (offset+2) table)
                           |(Const'(Sexpr(String(x))))-> let length = String.length x in
				
                              let sob = (ConstSOB(Sexpr(String(x)),offset,
                                                 (Printf.sprintf "MAKE_LITERAL_STRING %s" (convert_string x)   ))) in
                              let table = (List.append table [sob]) in           
                              (make_const_tbl cdr (offset+9+length) table)
                          |If'(test,first,second)-> let table_test =  (make_const_tbl [test] offset table) in
                                                     let offset = last_offset table_test in
                                                     let table_first = (make_const_tbl [first] offset table_test) in
                                                     let offset = last_offset table_first in
                                                     let table_second = (make_const_tbl [second] offset table_first) in
                                                     let offset = last_offset table_second in
                                                     (make_const_tbl cdr offset table_second)
                           |Set'(var,value)-> let table_var =  (make_const_tbl [var] offset table) in
                                                     let offset = last_offset table_var in
                                                     let table_value = (make_const_tbl [value] offset table_var) in
                                                     let offset = last_offset table_value in
                                                     (make_const_tbl cdr offset table_value)
                           |Seq'(exprs)-> let table = List.fold_left help_f table exprs in
                                          let offset = last_offset table in
                                          (make_const_tbl cdr offset table)
                           |Def'(var,value)->let table_var =  (make_const_tbl [var] offset table) in
                                                     let offset = last_offset table_var in
                                                     let table_value = (make_const_tbl [value] offset table_var) in
                                                     let offset = last_offset table_value in
                                                     (make_const_tbl cdr offset table_value)
                           |Or'(exprs)->let table = List.fold_left help_f table exprs in
                                          let offset = last_offset table in
                                          (make_const_tbl cdr offset table)
                           |LambdaSimple'(_,body)-> let table = make_const_tbl [body] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl cdr offset table)
                           |LambdaOpt'(_,_,body)-> let table = make_const_tbl [body] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl cdr offset table)
                           |Applic'(proc,exprs)->let table = make_const_tbl [proc] offset table in
                                                 let table = List.fold_left help_f table exprs in
                                                 let offset = last_offset table in
                                                 (make_const_tbl cdr offset table)
                           |ApplicTP'(proc,exprs)->let table = make_const_tbl [proc] offset table in
                                                   let table = List.fold_left help_f table exprs in
                                                   let offset = last_offset table in
                                                   (make_const_tbl cdr offset table)
                           |BoxSet'(_,value)->let table = make_const_tbl [value] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl cdr offset table)                
                           |car-> (make_const_tbl cdr offset table))
  |exp -> table
        
and help_f table exp =
  let offset = last_offset table in
  make_const_tbl [exp] offset table;;

let rec into_expr' = function
  |(car ::cdr) -> List.append [Const'(Sexpr(car))] (into_expr' cdr)
  |[]-> [];;
     

let rec vector_offsets list table =
  match list with
  |(car::[])-> let offset = sob_offset car table in
               (Printf.sprintf "const_tbl+%d" offset)
  |(car::cdr)-> let offset = sob_offset car table in
                String.concat "," [(Printf.sprintf "const_tbl+%d" offset); (vector_offsets cdr table)]
  |list->"";;
  
let rec make_const_tbl2 exp offset table =
  match exp with
  |(car :: cdr)-> let bool = sob_exists car table in
                        if bool then (make_const_tbl2 cdr offset table) else
                          (match car with
                           |Const'(Sexpr(Symbol(x)))->
                              let ans = (sob_offset (Const'(Sexpr(String(x)))) table) in
                              let length = String.length x in
                             if ans = -1 then
                               let table_with_string = (make_const_tbl [(Const'(Sexpr(String(x))))] offset table) in 
                               let sob = (ConstSOB(Sexpr(Symbol(x)),(offset+9+length),
                                                   (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" offset))) in
                               let table = (List.append table_with_string [sob]) in           
                               (make_const_tbl2 cdr (offset+18+length) table)
                             else
                               let sob = (ConstSOB(Sexpr(Symbol(x)),(offset),
                                                   (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" ans))) in
                               let table = (List.append table [sob]) in           
                               (make_const_tbl2 cdr (offset+9) table)
                           |Const'(Sexpr(Pair(x,y)))->
                             let table_with_car1 = make_const_tbl [(Const'(Sexpr(x)))] offset table in
                             let table_with_car2 = make_const_tbl2 [(Const'(Sexpr(x)))] offset table_with_car1 in
                             let offset = last_offset table_with_car2 in
			     let table_with_cdr1 = make_const_tbl [(Const'(Sexpr(y)))] offset table_with_car2 in
                             let table_with_cdr2 = make_const_tbl2 [(Const'(Sexpr(y)))] offset table_with_cdr1 in
                             let offset_with_cdr = last_offset table_with_cdr2 in  
                             let x_offset = sob_offset (Const'(Sexpr(x))) table_with_cdr2 in
                             let y_offset = sob_offset (Const'(Sexpr(y))) table_with_cdr2 in 
                             let sob = (ConstSOB(Sexpr(Pair(x,y)), offset_with_cdr,
                                                 (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)" x_offset y_offset ))) in
                             let table = (List.append table_with_cdr2 [sob]) in 
                             make_const_tbl2 cdr (offset_with_cdr + 17) table
                           |Const'(Sexpr(Vector(x)))-> 
                             let expr' = into_expr' x in
                             let length = List.length expr' in
                             let table1 = make_const_tbl expr' offset table in
                             let offset = last_offset table1 in              
                             let table2 = make_const_tbl2 expr' offset table1 in
                             let string_offset_of_elements = vector_offsets expr' table2 in
                             let vector_offset = last_offset table2 in
                             let sob = (ConstSOB(Sexpr(Vector(x)), vector_offset,
                                                 (Printf.sprintf "MAKE_LITERAL_VECTOR %d, %s" (List.length x) string_offset_of_elements))) in
                             let table = (List.append table2 [sob]) in
                             make_const_tbl2 cdr (vector_offset+9+length*8) table
                           |If'(test,first,second)-> let table_test =  (make_const_tbl2 [test] offset table) in
                                                     let offset = last_offset table_test in
                                                     let table_first = (make_const_tbl2 [first] offset table_test) in
                                                     let offset = last_offset table_first in
                                                     let table_second = (make_const_tbl2 [second] offset table_first) in
                                                     let offset = last_offset table_second in
                                                     (make_const_tbl2 cdr offset table_second)
                           |Set'(var,value)-> let table_var =  (make_const_tbl2 [var] offset table) in
                                                     let offset = last_offset table_var in
                                                     let table_value = (make_const_tbl2 [value] offset table_var) in
                                                     let offset = last_offset table_value in
                                                     (make_const_tbl2 cdr offset table_value)
                           |Seq'(exprs)-> let table = List.fold_left help2 table exprs in
                                          let offset = last_offset table in
                                          (make_const_tbl2 cdr offset table)
                           |Def'(var,value)->let table_var =  (make_const_tbl2 [var] offset table) in
                                                     let offset = last_offset table_var in
                                                     let table_value = (make_const_tbl2 [value] offset table_var) in
                                                     let offset = last_offset table_value in
                                                     (make_const_tbl2 cdr offset table_value)
                           |Or'(exprs)->let table = List.fold_left help2 table exprs in
                                          let offset = last_offset table in
                                          (make_const_tbl2 cdr offset table)
                           |LambdaSimple'(_,body)-> let table = make_const_tbl2 [body] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl2 cdr offset table)
                           |LambdaOpt'(_,_,body)-> let table = make_const_tbl2 [body] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl2 cdr offset table)
                           |Applic'(proc,exprs)->let table = make_const_tbl2 [proc] offset table in
                                                 let table = List.fold_left help2 table exprs in
                                                 let offset = last_offset table in
                                                 (make_const_tbl2 cdr offset table)
                           |ApplicTP'(proc,exprs)->let table = make_const_tbl2 [proc] offset table in
                                                   let table = List.fold_left help2 table exprs in
                                                   let offset = last_offset table in
                                                   (make_const_tbl2 cdr offset table)
                           |BoxSet'(_,value)->let table = make_const_tbl2 [value] offset table in
                                                         let offset = last_offset table in
                                                         (make_const_tbl2 cdr offset table)  
                           |car-> make_const_tbl2 cdr offset table)
  |exp -> table


and help2 table exp =
  let offset = last_offset table in
  make_const_tbl2 [exp] offset table;;         
                               
let consts_table exprs  =
   let start = [ConstSOB(Void,0,"MAKE_VOID");
              ConstSOB(Sexpr(Nil),1,"MAKE_NIL");
              ConstSOB(Sexpr(Bool(false)),2,"MAKE_BOOL(0)");
              ConstSOB(Sexpr(Bool(true)),4,"MAKE_BOOL(1)")] in
  let table = make_const_tbl exprs 6 start in
  let offset = last_offset table in
  make_const_tbl2 exprs offset table;;
(*
let rec list_for_apply seq =
  match seq with
  |[]-> raise X_syntax_error
  |(x::[])->  Applic'(Var'(VarFree("append")),[x;Const'(Sexpr(Nil))])
  |(car::cdr)-> Applic'(Var'(VarFree("cons")),[car;list_for_apply cdr]);;*)
(*
let rec p_l_into_parts pair =
  match pair with
  |Pair(x,Nil)-> [Const'(Sexpr(x))]
  |Pair(x,Pair(w,y))-> List.cons (Const'(Sexpr(x)))  (p_l_into_parts (Pair(w,y)))
  |pair-> raise X_syntax_error;;*)
(*
let rec loop_1 num counter=
  if counter = num then "" else String.concat "\n" [Printf.sprintf "mov r12,qword[rbp-8*%d]\nMAKE_PAIR(r14,r12,r13)\n mov r13,r14" (counter+2) ; loop_1 num (counter+1)];;

let rec loop_2 l total num counter=
  if counter = (l+3-num) then "" else String.concat "\n" [Printf.sprintf "mov r12,qword[rbp-8*%d]\nmov qword[rbp-8*%d],r12" total (total-num); loop_2 l (total+1) num (counter+1)];;

(* l = num of args. num = args-necessary *)
let change_frame l num =
  let a = loop_1 num 0 in
  let b = loop_2 l (1+num+1) num 0 in
  let c = String.concat "\n" [Printf.sprintf "mov qword[rbp-8*%d],%d" (l+2) (l-num) ;Printf.sprintf "mov r13, SOB_NIL_ADDRESS";a;b;"mov qword[rbp-8],r13"; Printf.sprintf "add rsp, %d" (8*num)] in 
  c;;

let opt_frame l num =
  if num < 1 then "" else (change_frame l num);;
*)

let rec get_free_vars str expr' =
    match expr' with
    |(car::cdr)-> (match car with
                  |Const'(x)-> get_free_vars str cdr
                  |Var'(VarFree(x))->get_free_vars (List.append str [x]) cdr 
                  |Var'(x) -> get_free_vars str cdr
                  |If'(test,first,second)->
                    List.concat  [get_free_vars str cdr;get_free_vars [] [test];
                                  get_free_vars [] [first];get_free_vars [] [second]]
                  |Set'(x,y)-> List.concat  [get_free_vars str cdr;get_free_vars [] [x];get_free_vars [] [y]]                        
                  |Seq'(exprs)-> List.append (get_free_vars str cdr) (get_free_vars [] exprs) 
                  |Def'(var,body)-> List.concat  [get_free_vars str cdr;get_free_vars [] [var];get_free_vars [] [body]]
                  |Or'(exprs)->  List.append  (get_free_vars str cdr) (get_free_vars [] exprs)
                  |LambdaSimple'(params,body) -> List.concat  [get_free_vars str cdr;get_free_vars [] [body]]                        
                  |LambdaOpt'(params,vs,body)-> List.concat  [get_free_vars str cdr;get_free_vars [] [body]]                        
                  |Applic'(expr,expr_list)->List.concat  [get_free_vars str cdr;get_free_vars [] [expr];
                                                          get_free_vars [] expr_list] 
                  |ApplicTP'(expr,expr_list)-> List.concat  [get_free_vars str cdr;get_free_vars [] [expr];
                                                          get_free_vars [] expr_list] 
                  |Box'(x)->get_free_vars str cdr
                  |BoxGet'(x)-> get_free_vars str cdr
                  |BoxSet'(x,y)-> List.append (get_free_vars str cdr)(get_free_vars [] [y]))
    |expr'-> str;;



let rec fv_label str free_tbl =
  match free_tbl with
  |(FVP(free_var,index,_)::cdr)-> if free_var = str then index else fv_label str cdr
  |free_tbl -> raise X_syntax_error;;

let count = ref 1;;
let args_on_stack = ref 0;;
let prev_args_on_stack = ref 0;;

let rec gen expr' fv_table c_table depth=
  
    let c = !count in
     count := (!count+1); 
		   match expr' with
                   |Const'(_)-> Printf.sprintf "mov rax, const_tbl+%d" (sob_offset expr' c_table)
                                   
                                                    
                   |Var'(VarFree(x))->  
                                  Printf.sprintf "mov rax, qword[fvar_tbl+ %d*WORD_SIZE]" (fv_label x fv_table)
                                  
                   |Var'(VarBound(_,major,minor))-> String.concat "\n"
                                                      ["mov rax,qword[rbp+8*2]"; Printf.sprintf "mov rax,qword[rax+8*%d]" major;
                                                        Printf.sprintf "mov rax,qword[rax+8*%d]" minor]
                   |Var'(VarParam(_,minor))-> Printf.sprintf "mov rax,qword[rbp+8*(4+%d)]" minor
                   |If'(test,first,second)-> 
					     let q = "\n" ^ (gen test fv_table c_table depth) in
                                             let t = "\n" ^ (gen first fv_table c_table depth) in
                                             let f = "\n" ^ (gen second fv_table c_table depth) in
					    
                                             String.concat "\n" [q;"cmp rax, SOB_FALSE_ADDRESS";Printf.sprintf "je Lelse%d" c;t; Printf.sprintf "jmp Lexit%d" c;
                                                                 Printf.sprintf "Lelse%d:" c; f; Printf.sprintf "Lexit%d:" c]
                   |Set'(x,y)-> let value = "\n" ^ (gen y fv_table c_table depth) in
		        
                    (match x with
                     |Var'(VarFree(str))->
                       String.concat "\n"
                         [value;Printf.sprintf "mov qword[fvar_tbl + %d*WORD_SIZE],rax" (fv_label str fv_table);
                              "mov rax, const_tbl"]
                     |Var'(VarParam(_, minor))->
                       String.concat "\n"
                         [value; Printf.sprintf "mov qword[rbp+8*(4+%d)],rax"  minor;
                              "mov rax, const_tbl"]                    
                     |Var'(VarBound(_,major, minor))->
                       String.concat "\n"
                         [value; "mov r13, qword[rbp+8*2]";Printf.sprintf "mov r13, qword[r13+8*%d]" major;
                         Printf.sprintf "mov qword[r13 + 8*%d],rax" minor ; "mov rax, const_tbl"]
                     |x->raise X_syntax_error)                  
                   |Seq'(exprs)-> let values = List.map (fun(x)-> "\n" ^ (gen x fv_table c_table depth)) exprs in
                                          String.concat "\n" values
                                  
                    |Def'(var,value)-> (match var with
                                        |Var'(VarFree(var))-> let value = "\n" ^ (gen value fv_table c_table depth) in
                                                             
                                                           String.concat "\n"
                                                             [value ;Printf.sprintf "mov [fvar_tbl + %d*WORD_SIZE],rax" (fv_label var fv_table);
                                                              "mov rax, const_tbl"]
                                        |var-> raise X_syntax_error)
                     |Or'(exprs)->  String.concat "\n" [String.concat 
					(Printf.sprintf "cmp rax, SOB_FALSE_ADDRESS\njne Lexit%d\n" c)
                                                      (List.map (fun(x)->  "\n" ^ gen x fv_table c_table depth ^ "\n") exprs)
                                                                            ;Printf.sprintf "Lexit%d:" c]
                                  
                    |LambdaSimple'(params,body) ->  let length = List.length params in
                                                    
                                                    if depth = 0 then
                                                      String.concat "\n" [Printf.sprintf "MAKE_CLOSURE(rax,rbx, lambda_body_%d)" c;
                                                                          Printf.sprintf "jmp end_lambda_body_%d" c;
                                                                          Printf.sprintf "lambda_body_%d:" c;
                                                                          "NEW_FRAME";
                                                                          Printf.sprintf "mov r13, %d" length;
                                                                          "mov r12,PARAM_COUNT";
                                                                          "cmp r13,r12";
                                                                          Printf.sprintf "je lambda%d_cont" c;
									  Printf.sprintf "call lambda_error_%d" c;
								          "CLOSE_FRAME";
									  Printf.sprintf "lambda%d_cont:" c;
                                                                           "\n" ^ (gen body fv_table c_table (depth+1));
                                                                          "CLOSE_FRAME";
                                                                          Printf.sprintf "lambda_error_%d:" c;
									  "NEW_FRAME";
								          "push rax\npush rbx";
	                                                                  Printf.sprintf "mov rdi, .format_lambda%d"  c;
	                                                                  "mov rax, 0";
	                                                                  "call printf";
								          "pop rbx\npop rax";
	                                                                  "CLOSE_FRAME";
								          Printf.sprintf ".format_lambda%d: db \" params != args %d \",0" c c;
                                                                          Printf.sprintf "end_lambda_body_%d:" c]
                                                                          
                                                      else
                                                        String.concat "\n" [         
                                                                          Printf.sprintf "EXTEND_ENV %d,PARAM_COUNT" (depth-1);
                                                                          "COPY_PARAMS_FROM_STACK PARAM_COUNT";
                                                                          Printf.sprintf "MAKE_CLOSURE(rax,rbx, lambda_body_%d)" c;
                                                                          Printf.sprintf "jmp end_lambda_body_%d" c;
                                                                          Printf.sprintf "lambda_body_%d:" c;
                                                                          "NEW_FRAME";
                                                                          Printf.sprintf "mov r13, %d" length;
                                                                          "mov r12,PARAM_COUNT";
                                                                          "cmp r13,r12";
									
                                                                          Printf.sprintf "je lambda%d_cont" c;
									  Printf.sprintf "call lambda_error_%d" c;
								          "CLOSE_FRAME";
									  Printf.sprintf "lambda%d_cont:" c;
                                                                           "\n" ^ (gen body fv_table c_table (depth+1));
                                                                          "CLOSE_FRAME";
                                                                          Printf.sprintf "lambda_error_%d:" c;
                                                                          "NEW_FRAME";
								          "push rax\npush rbx";
	                                                                  Printf.sprintf "mov rdi, .format_lambda%d" c;
	                                                                  "mov rax, 0";
	                                                                  "call printf";
								          "pop rbx\npop rax";
	                                                                  "CLOSE_FRAME";
								          Printf.sprintf ".format_lambda%d: db \" params != args %d \",0" c c;
                                                                          Printf.sprintf "end_lambda_body_%d:" c]
                                                                                                            
                     |LambdaOpt'(params,vs,body)-> let length = List.length params in
                                                  
						                                      
                                                      if depth = 0 then
                                                      String.concat "\n" [Printf.sprintf "MAKE_CLOSURE(rax,rbx, lambdaOpt_body_%d)" c;
                                                                          Printf.sprintf "jmp end_lambdaOpt_body_%d" c;
                                                                          Printf.sprintf "lambdaOpt_body_%d:" c;
								          Printf.sprintf "mov r8,qword[rsp+16] \nmov r9,r8\nsub r9,%d\nCHANGE_FRAME r8,r9" length;
                                                                          "NEW_FRAME";
                                                                          Printf.sprintf "mov r13, %d" length;
                                                                          "mov r12,PARAM_COUNT";
                                                                          "cmp r13,r12";
                                                                          Printf.sprintf "je lambdaOpt%d_cont" c;
									  Printf.sprintf "call lambdaOpt_error_%d" c;
								          "CLOSE_FRAME";
									  Printf.sprintf "lambdaOpt%d_cont:" c;
									  
                                                                           "\n" ^ (gen body fv_table c_table (depth+1));
                                                                          "CLOSE_FRAME";
                                                                          Printf.sprintf "lambdaOpt_error_%d:" c;
                                                                          "NEW_FRAME";
								          "push rax\npush rbx";
	                                                                  Printf.sprintf "mov rdi, .format_lambda%d" c;
	                                                                  "mov rax, 0";
	                                                                  "call printf";
								          "pop rbx\npop rax";
	                                                                  "CLOSE_FRAME";
								          Printf.sprintf ".format_lambda%d: db \" params != args %d \",0" c c;
                                                                          Printf.sprintf "end_lambdaOpt_body_%d:" c]
                                                                          
                                                      else
                                                        
                                                        String.concat "\n"            
                                                                          [Printf.sprintf "EXTEND_ENV %d,PARAM_COUNT" (depth-1);
                                                                          "COPY_PARAMS_FROM_STACK PARAM_COUNT";
                                                                          Printf.sprintf "MAKE_CLOSURE(rax,rbx, lambdaOpt_body_%d)" c;
                                                                          Printf.sprintf "jmp end_lambdaOpt_body_%d" c;
                                                                          Printf.sprintf "lambdaOpt_body_%d:" c;
									  Printf.sprintf "mov r8,qword[rsp+16] \nmov r9,r8\nsub r9,%d\nCHANGE_FRAME r8,r9" length;
                                                                          "NEW_FRAME";
                                                                           Printf.sprintf "mov r13, %d" length;
                                                                          
                                                                          "mov r12,PARAM_COUNT";
                                                                          "cmp r13,r12";
                                                                          
                                                                          Printf.sprintf "je lambdaOpt%d_cont" c;
									  Printf.sprintf "call lambdaOpt_error_%d" c;
								          "CLOSE_FRAME";
									  Printf.sprintf "lambdaOpt%d_cont:" c;
									  
                                                                           "\n" ^ (gen body fv_table c_table (depth+1));
                                                                          "CLOSE_FRAME";
                                                                          Printf.sprintf "lambdaOpt_error_%d:" c;
                                                                         "NEW_FRAME";
								         "push rax\npush rbx";
                                                                          Printf.sprintf "mov rdi, .format_lambda%d" c;
	                                                                  
	                                                                  "mov rax, 0";
	                                                                  "call printf";
								          "pop rbx\npop rax";
	                                                                  "CLOSE_FRAME";
								          Printf.sprintf ".format_lambda%d: db \" params != args %d \",0" c c;
                                                                          Printf.sprintf "end_lambdaOpt_body_%d:" c]
                                                                         

                                                                          
                                                             
                                                       
                 |Applic'(expr,expr_list)->  let length = List.length expr_list in 
					     prev_args_on_stack := !args_on_stack;
				             args_on_stack := length;
                                             let rev = List.rev expr_list in
                                             let values = List.map (fun(x)->  "\n" ^ (gen x fv_table c_table depth)) rev in

                                             let proc =  "\n" ^ (gen expr fv_table c_table depth) in
                                             String.concat "\n" ["push SOB_NIL_ADDRESS"; String.concat "\n" (List.map (fun(x)-> Printf.sprintf "%s\npush rax" x) values) ; 
					     Printf.sprintf "push %d" length ; proc;
                                                                 "cmp byte[rax], T_CLOSURE"; "jne not_closure_error";
                                                                 "push qword[rax+1]";"call qword[rax+9]";"add rsp,8";"pop r12";"inc r12";"shl r12,3";"add rsp,r12\n"]

                                                          
                 |ApplicTP'(expr,expr_list)->
					     let length = List.length expr_list  in
					     prev_args_on_stack := !args_on_stack;
					     args_on_stack := length;
                                             let rev = List.rev expr_list in
                                             let values = List.map (fun(x)->  "\n" ^ (gen x fv_table c_table depth)) rev in
					     
                                             let proc =  "\n" ^ (gen expr fv_table c_table depth) in
                                             String.concat "\n" ["mov qword[tp],1";"push SOB_NIL_ADDRESS"; String.concat "\n" (List.map (fun(x)-> Printf.sprintf "%s\npush rax" x) values) ;
					      Printf.sprintf "push %d" length; proc;
                                                                 "cmp byte[rax], T_CLOSURE"; "jne not_closure_error";
                                                                 "push qword[rax+1]";"push qword[rbp+8]";"mov r8, qword[rbp]";
								 "mov r9,PARAM_COUNT";"mov r10,qword[rsp+16]";"add r10,4";"SHIFT_FRAME r10,PARAM_COUNT" ;"add r9,5";"shl r9,3";"add rsp,r9";"mov rbp,r8";"jmp qword[rax+9]\n"] 
                  |Box'(x)-> String.concat "\n" [gen (Var'(x)) fv_table c_table depth;"MALLOC r12, WORD_SIZE";"mov qword[r12],rax";
						"mov rax,r12"]
                  |BoxGet'(x)-> let var =  "\n" ^ (gen (Var'(x)) fv_table c_table depth) in
                             String.concat "\n" [var; "mov rax,qword[rax]"]
                  |BoxSet'(x,y)-> let value =  "\n" ^ (gen y fv_table c_table depth) in
                                  let var =  "\n" ^ (gen (Var'(x)) fv_table c_table depth) in
                                  String.concat "\n" [value;"push rax";var;"pop qword[rax]";"mov rax,SOB_VOID_ADDRESS"];; 
    


let rec remove_dup exprs' str =
  match exprs' with
  |(car::cdr)-> let bool = List.exists (fun(x)-> x = car) str in
                if bool then remove_dup cdr str else remove_dup cdr
                                                       (List.append str [car])
  |exprs' -> str;;

let rec create_pairs str counter =
  match str with
  |(car::cdr)-> List.cons (FVP(car, counter,Printf.sprintf "var%d" counter))
                  (create_pairs cdr (counter+1))
              
  |str->[];;

let create_consts_table s =
  let exprs = run s in
  let start = [ConstSOB(Void,0,"MAKE_VOID");
              ConstSOB(Sexpr(Nil),1,"MAKE_NIL");
              ConstSOB(Sexpr(Bool(false)),2,"MAKE_BOOL(0)");
              ConstSOB(Sexpr(Bool(true)),4,"MAKE_BOOL(1)")] in
  let table = make_const_tbl exprs 6 start in
  let offset = last_offset table in
  make_const_tbl2 exprs offset table;;

let test2 s =
  let exprs = run s in
  get_free_vars [] exprs;;


let primitive_names_to_labels = 
  [ "car","car";"cdr","cdr";"cons","cons";"set-car!","set-car!";"set-cdr!","set-cdr!";"apply","apply";"boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
(* you can add yours here *)];;


 (* let exprs = run s in
  let prim_fvars = List.map (fun(x,_)->x) primitive_names_to_labels in 
  let with_dup = get_free_vars prim_fvars exprs in
  let without_dup = remove_dup with_dup [] in
  create_pairs without_dup 0;;*)

let check s =
   let exprs = run s in
   let prim_fvars = List.map (fun(x,_)->x) primitive_names_to_labels in
   let a =  get_free_vars prim_fvars exprs in
   let c = remove_dup a [] in
   create_pairs c 0;;
 
let create_fvar_table s =
  check s;;

let fvar_table exprs =
 (*  let prim_fvars = List.map (fun(x,_)->x) primitive_names_to_labels in *)
  let prim_fvars = List.map (fun(x,_)->x) primitive_names_to_labels in
   let a =  get_free_vars prim_fvars exprs in
   let c = remove_dup a [] in
   create_pairs c 0;;
 


(*let test4 s =
  let exprs = run_on_all s in
  let fvars_with_dup = get_free_vars [] exprs in
  let fvars = remove_dup fvars_with_dup [] in
  let fvar_table = create_pairs fvars 3 in
  let const_table = consts_table exprs in
  gen exprs fvar_table const_table 0;; *)
(*
let rec no_type_const = function
  |(ConstSOB(x,y,z)::cdr)-> List.cons (x,(y,z)) (no_type_const cdr)
  |[]->[];;

let rec no_type_fvar = function
  |(FVP(x,y,z)::cdr)-> List.cons (x,z) (no_type_fvar cdr)
  |[]->[];; *)

 
 let make_consts_tbl asts =
   consts_table asts;;
 
 
 let make_fvars_tbl asts =
   fvar_table asts;;
  
 
 let generate consts fvars e =
   gen e fvars consts 0 ;;
(* let generate_print consts fvars e =
   gen_print e fvars consts 0 ;;


 let total_check exprs =
   let exprs = run exprs in
   let consts = make_consts_tbl exprs in
   let fvars = make_fvars_tbl exprs in
   gen_print exprs fvars consts 0;;
 *)
end;;
