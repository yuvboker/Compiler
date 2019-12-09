(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
  
   type sob =
  ConstSOB of constant * int * string;;
  type free_var_pair =
   FVP of string * int * string;; 
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;; 

module Semantics : SEMANTICS = struct

(*
let annotate_lexical_addresses e = raise X_syntax_error;;

let annotate_tail_calls e = raise X_syntax_error;;

let box_set e = raise X_syntax_error;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)   *)                              
 
type lexical =
  Wrap of string * int * int;;
type get_set =
  |Group of string * int * int * int list * int list;;
type wrap =
  Param of string * int;;




let rec var_type list_of_vars var_name =
  match list_of_vars with
  |[] -> Var'(VarFree(var_name))
  (*let bool = List.exists (fun(x)-> x = var_name) global in
          if bool then Var'(VarFree(var_name)) else raise X_syntax_error*)
  |(car::cdr) -> (match car with
                 |Wrap(var,major,minor)-> if var_name = var
                                      then if major = 0 then Var'(VarParam(var,minor)) else Var'(VarBound(var,major-1,minor))
                                          else var_type cdr var_name);;
let rec add_vars list_of_vars params counter =
  match params with
  |[]-> list_of_vars
  |(car::cdr)-> let add_param = List.cons (Wrap(car,0,counter)) list_of_vars in
                add_vars add_param cdr (counter+1);;

let rec update_major list_of_vars =
  match list_of_vars with
  |[]->list_of_vars
  |(Wrap(var,major,minor)::cdr)-> let update = Wrap(var,(major+1),minor) in
                                  List.cons update (update_major cdr);;

let update list_of_vars params =
  add_vars (update_major list_of_vars) params 0;;
                                  



let get_param p =
  match p with
  |Param(x,_)-> x;;

    

(*
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * expr list
 *)


let rec annotate_lex_h wraps exprs =
  match exprs with
  |Const(x)->Const'(x)
  |Var(x)-> var_type wraps x
  |If(test,first,second)-> If'(annotate_lex_h wraps test, annotate_lex_h wraps first,annotate_lex_h wraps second)
  |Seq(exprs)-> Seq'(List.map (fun(x)->annotate_lex_h wraps x) exprs)
  (*match car with|Def(var,body)-> let new_global List.cons var global in
   List.cons (Def'(look_for_vars new_global wraps body))*)         
  |Set(x,y)-> Set'(annotate_lex_h wraps x, annotate_lex_h wraps y)
  |Def(Var(x),body)-> Def'(Var'(VarFree(x)),annotate_lex_h wraps body)
                          (*let new_global List.cons var global in Def'(look_for_vars new_global wraps body)*)
  |Or(exprs)->Or'(List.map (fun(x)->annotate_lex_h wraps x) exprs)
  |LambdaSimple(params,body)-> LambdaSimple'(params,annotate_lex_h (update wraps params) body)
  |LambdaOpt(params,vs,body)-> LambdaOpt'(params,vs,annotate_lex_h (update wraps (List.append params [vs])) body)
  |Applic(expr, expr_list)-> Applic'(annotate_lex_h wraps expr, (List.map (fun(x)->annotate_lex_h wraps x) expr_list))
  |exprs -> raise X_syntax_error;;

let rec annotate in_tp  exprs =
  match exprs with
  |Const'(x)->Const'(x)
  |Var'(x)-> Var'(x)
  |If'(test,first,second)-> If'(annotate false test,annotate in_tp first,annotate in_tp  second)
  |Seq'(exprs)-> let l = List.rev exprs in
                 Seq'(List.rev (List.cons (annotate in_tp (List.hd l)) (List.map (fun(x)->annotate false x)(List.tl l))))
  (*match car with|Def(var,body)-> let new_global List.cons var global in
   List.cons (Def'(look_for_vars new_global wraps body))*)         
  |Set'(x,y)-> Set'(annotate false  x, annotate false  y)
  |Def'(x,body)-> Def'(x,annotate in_tp body)
                          (*let new_global List.cons var global in Def'(look_for_vars new_global wraps body)*)
  |Or'(exprs)->  let l = List.rev exprs in
                 Or'(List.rev (List.cons (annotate in_tp (List.hd l)) (List.map (fun(x)->annotate false x)(List.tl l))))
  |LambdaSimple'(params,body)-> LambdaSimple'(params,annotate true body)
  |LambdaOpt'(params,vs,body)-> LambdaOpt'(params,vs,annotate true body)
  |Applic'(expr, expr_list)-> if in_tp = false then  Applic'(annotate false expr, (List.map (fun(x)->annotate false  x) expr_list))
                              else  ApplicTP'(annotate false expr, (List.map (fun(x)->annotate false x) expr_list))
  |exprs -> raise X_syntax_error;;                           


let annotate_lex expr =
  annotate_lex_h [] expr;;

let annotate_tc expr =
  annotate false expr;;

(*
let rec annotate_tc exprs =
  match exprs with
  |Const'(x)-> Const'(x)
  |Var'(x)->Var'(x)
  |If'(test,first,second)-> If'(annotate_tc test,annotate_tc first,annotate_tc second)
  |Seq'(exprs)-> Seq'(List.map annotate_tc exprs)
  |Set'(x,y)-> Set'(annotate_tc x, annotate_tc y)
  |Def'(var,body)->Def'(var,annotate_tc body)
  |Or'(exprs)->Or'(List.map annotate_tc exprs)
  |LambdaSimple'(params,body)->LambdaSimple'(params,annotate_tc body)
  |LambdaOpt'(params,vs,body)->LambdaOpt'(params,vs,annotate_tc body)
  |Applic'(expr,(car::cdr))-> (match car with
                              |Const'(Sexpr(Bool(false)))->Applic'(annotate_tc expr, List.map annotate_tc cdr)
                              |Const'(Sexpr(Bool(true)))->ApplicTP'(annotate_tc expr,List.map annotate_tc cdr)
                              |car->raise X_syntax_error)
  |exprs->raise X_syntax_error;; *)
                                  
     
let rec get_and_set group expr =
  match group ,expr with
  |Group (p,major,minor,get,set),x-> (match x with
                                      |Const'(x)->Group (p,major,minor,get,set)                 
                                      |Var'(VarFree(x)) -> Group (p,major,minor,get,set)
                                      |Var'(VarBound(x,_,_)) ->
                                        if x = p
                                        then Group (p,major,minor,(List.cons major get),set)
                                        else  Group (p,major,minor,get,set)
                                      |Var'(VarParam(x,_)) ->
                                        if x = p
                                        then Group (p,major,minor,(List.cons major get),set)
                                        else Group (p,major,minor,get,set)
                                      |If'(test,first,second)-> get_and_set (get_and_set(get_and_set (Group(p,major,minor,get,set)) test) first) second
                                      |Seq'(exprs) -> List.fold_left get_and_set (Group(p,major,minor,get,set)) exprs
                                      |Set'(Var'(x),y)-> (match x with                                      
                                                          |VarParam(x,_)->if x = p then
                                                                            get_and_set (Group(p,major,minor,get,(List.cons major set))) y
                                                                          else
                                                                            get_and_set (Group(p,major,minor,get,set)) y
                                                          |VarBound(x,_,_)->if x = p then
                                                                            get_and_set (Group(p,major,minor,get,(List.cons major set))) y
                                                                          else
                                                                            get_and_set (Group(p,major,minor,get,set)) y
                                                          |x-> get_and_set (Group(p,major,minor,get,set)) y)
                                      |Def'(var,body)-> get_and_set (Group(p,major,minor,get,set)) body
                                      |Or'(exprs)-> List.fold_left get_and_set (Group(p,major,minor,get,set)) exprs
                                      
                                      |LambdaSimple'(params,body)-> let bool =  List.exists (fun(x)-> x=p) params in
                                                                    if bool then Group(p,major,minor,get,set)           
                                                                    else if major = 0
                                                                    then
                                                                    let Group(_,_,_,get,set) = get_and_set (Group(p,(minor+1),minor,get,set)) body in
                                                                    Group(p,0,(minor+1),get,set)
                                                                    else
                                                                    get_and_set (Group(p,major,minor,get,set)) body
                                      |LambdaOpt'(params,vs,body)-> let bool =  List.exists (fun(x)-> x=p) (List.append params [vs]) in
                                                                    if bool then Group(p,major,minor,get,set)           
                                                                    else if major = 0
                                                                    then
                                                                    let Group(_,_,_,get,set) = get_and_set (Group(p,(minor+1),minor,get,set)) body in
                                                                    Group(p,0,(minor+1),get,set)
                                                                    else
                                                                    get_and_set (Group(p,major,minor,get,set)) body
                                      |Applic'(proc,args)-> List.fold_left get_and_set (get_and_set (Group(p,major,minor,get,set)) proc) args
                                      |ApplicTP'(proc,args)->List.fold_left get_and_set (get_and_set (Group(p,major,minor,get,set)) proc) args
                                      |Box'(x)-> Group(p,major,minor,get,set)
                                      |BoxGet'(x)-> Group(p,major,minor,get,set)
                                      |BoxSet'(x,y)-> get_and_set (Group(p,major,minor,get,set)) y
                                      |x -> raise X_syntax_error);;
    
let compare x y = (x-y);;

         
let should_box p exp =
  let Group(_,_,_,get,set) = get_and_set (Group(p,0,0,[],[])) exp in
  match get,set with
  |[],set -> false
  |get,[]-> false
  |get,set ->
  let a = List.sort_uniq compare get in
  let b = List.sort_uniq compare set in
  (match a,b with
  |[x],[y] -> if x = y then false else true
  |a,b -> 
    if ((List.length a) > 1 || (List.length b) > 1) then true
    else false);;

let box_step1 p exp =
  match p with
  |Param(p,minor)-> Seq'((List.append [(Set'(Var'(VarParam(p,minor)),Box'(VarParam(p,minor))))] exp));;

let box_step1rest p exp =
   match p with
   |Param(p,minor)->((Set'(Var'(VarParam(p,minor)),Box'(VarParam(p,minor))))::exp);;
  
                  
  

let rec box_step2 p exp =
    match exp with
    |Const'(x)->Const'(x)
    |Var'(VarFree(x)) -> Var'(VarFree(x)) 
    |Var'(VarBound(x,major,minor)) ->
      if x = p
      then BoxGet'(VarBound(p,major,minor))
      else Var'(VarBound(x,major,minor))
    |Var'(VarParam(x,minor)) ->
      if x = p
      then BoxGet'(VarParam(p,minor))
      else Var'(VarParam(x,minor))
    |If'(test,first,second)-> If'(box_step2 p test, box_step2 p first,box_step2 p second)
    |Set'(Var'(x),y)-> (match x with                                      
                        |VarParam(x1,_)->if x1 = p then BoxSet'(x,box_step2 p y)
                                        else Set'(Var'(x),box_step2 p y)                   
                        |VarBound(x1,_,_)->if x1 = p then BoxSet'(x,box_step2 p y)
                                           else Set'(Var'(x),box_step2 p y)  
                        |x-> Set'(Var'(x),box_step2 p y))                                  
    |Seq'(exprs)->Seq'(List.map (fun(x)-> box_step2 p x) exprs)
    |Def'(var,body)->Def'(var,box_step2 p body)
    |Or'(exprs)->Or'(List.map (fun(x)-> box_step2 p x) exprs)
    |LambdaSimple'(params,body) -> let bool =  List.exists (fun(x)-> x=p) params in
                                   if bool then LambdaSimple'(params,body) else  LambdaSimple'(params,box_step2 p body)
    |LambdaOpt'(params,vs,body)-> let bool =  List.exists (fun(x)-> x=p) (List.append params [vs]) in
                                  if bool then LambdaOpt'(params,vs,body) else LambdaOpt'(params,vs,box_step2 p body)
    |Applic'(expr,expr_list)->Applic'(box_step2 p expr, List.map (fun(x)-> box_step2 p x) expr_list)
    |ApplicTP'(expr,expr_list)->ApplicTP'(box_step2 p expr, List.map (fun(x)-> box_step2 p x) expr_list)
    |Box'(x)->Box'(x)
    |BoxGet'(x)->BoxGet'(x)
    |BoxSet'(x,y)->BoxSet'(x, box_step2 p y)
    |exp -> raise X_syntax_error;; 
  
let test exp =
  let expr' = (annotate_tc(annotate_lex (Tag_Parser.tag_parse_expression (Reader.read_sexpr exp)))) in
  match expr' with
  |LambdaSimple'((car::cdr),body)-> should_box car body
  |expr' -> raise X_syntax_error;;

let rec wrap_with_minor params counter =
  match params with
  |[] -> []
  |(car::cdr)-> List.cons (Param(car,counter)) (wrap_with_minor cdr (counter+1));;


let list_of_params_box_needed params body =
  List.filter (fun(x)-> should_box (get_param x) body) params;;

let rec box_what_is_needed params body =
  match params with
  |[]-> body
  |(car::cdr)-> box_step2 (get_param car) (box_what_is_needed cdr body);;

let rec all_params params =
  match params with
  |[] -> []
  |(car::cdr)-> box_step1rest car (all_params cdr);;

let first_param params  =
  match params with
  |(car::cdr)-> box_step1 car (all_params cdr)
  |params -> raise X_syntax_error;;
                  
let box_params params body =
  let wrap_params = wrap_with_minor params 0 in
  let boxed_params = list_of_params_box_needed wrap_params body in
  let boxed_body = box_what_is_needed boxed_params body in
  if boxed_params = [] then boxed_body else
  let add_sets = first_param boxed_params in
  match add_sets with
  |Seq'(x)-> Seq'(List.append x [boxed_body])
  |add_sets -> raise X_syntax_error;;


let rec box expr' =
  match expr' with
    |Const'(x)->Const'(x)
    |Var'(x) -> Var'(x) 
    |If'(test,first,second)-> If'(box test, box first,box second)
    |Set'(x,y)-> Set'(x, box y)                                 
    |Seq'(exprs)->Seq'(List.map (fun(x)-> box x) exprs)
    |Def'(var,body)->Def'(var,box body)
    |Or'(exprs)->Or'(List.map (fun(x)-> box x) exprs)
    |LambdaSimple'(params,body) -> LambdaSimple'(params,box (box_params params body))
    |LambdaOpt'(params,vs,body)-> LambdaOpt'(params,vs,box (box_params (List.append params [vs]) body))
    |Applic'(expr,expr_list)->Applic'(box expr, List.map (fun(x)-> box x) expr_list)
    |ApplicTP'(expr,expr_list)->ApplicTP'(box expr, List.map (fun(x)-> box x) expr_list)
    |Box'(x)->Box'(x)
    |BoxGet'(x)->BoxGet'(x)
    |BoxSet'(x,y)->BoxSet'(x,box y);; 
  
let check1 exp =
  annotate_lex (Tag_Parser.tag_parse_expression (Reader.read_sexpr exp));;

let check2 exp =
  annotate_tc (annotate_lex (Tag_Parser.tag_parse_expression (Reader.read_sexpr exp)));;

let run exp =
  let expr' = (annotate_tc(annotate_lex (Tag_Parser.tag_parse_expression (Reader.read_sexpr exp)))) in
  box expr';;
      
let annotate_lexical_addresses e = annotate_lex e;;

let annotate_tail_calls e = annotate_tc e;;

let box_set e = box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;



 (* struct Semantics *)                                           

(* (Tag_Parser.tag_parse_expression (Reader.read_sexpr exp)) *)
end;;
