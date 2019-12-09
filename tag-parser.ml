(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_same_var_name_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct
  

(* work on the tag parser starts here *)




let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec check_dup  = function
  | [] -> false
  | [_] -> false
  | (h1::h2) -> let b = List.exists (fun (y)-> h1 = y) h2 in
                 match b with
                            | true -> true
                            | false -> (check_dup h2) ;;

   
let helper_dup list =
  let b = check_dup list in
            match b with
            |true -> raise X_syntax_error
            |false -> list;;

let rec pair_to_list  = function
  |Nil -> [[];[]]
  |Pair(Symbol(x1),Nil)-> [[x1]; []]

  |Pair(Symbol(x1),x2) -> (match x2 with
                          |Pair(_,_) -> let list_type = (pair_to_list x2) in
                                        (match list_type with
                                       |[y1;[y2]] -> [(List.append [x1] y1) ; [y2]]
                                       |[y1;[]] -> [(List.append [x1] y1) ; [] ]  
                                       |list_type ->raise X_syntax_error)
                          |Symbol(x3) -> [[x1] ; [x3]]
                          |x2 -> raise X_syntax_error)
  |_ -> raise X_syntax_error;;

let rec tag_parse = function
  |Nil -> Const (Void)
  |Number(x) -> Const (Sexpr (Number(x)))
  |Bool(x) -> Const (Sexpr (Bool(x)))
  |Char(x) -> Const (Sexpr (Char(x)))
  |String(x) -> Const (Sexpr (String(x)))
  |Symbol(x) -> let ans = List.exists (fun (y)-> x = y) reserved_word_list in
                (match ans with
                            | true -> raise  X_syntax_error
                            | false -> Var(x))
  |Pair(Symbol ("quote"), Pair(x,Nil)) -> Const(Sexpr(x))                                 
  |Pair (Symbol ("if"), Pair(test ,Pair(dit,Pair(dif,Nil)))) -> If((tag_parse test) , (tag_parse dit), (tag_parse dif))
  |Pair (Symbol ("if"), Pair(test ,Pair(dit,Nil))) -> If((tag_parse test) , (tag_parse dit), Const(Void))
  |Pair(Symbol ("lambda") , Pair(Symbol(_), Pair(Nil,Nil))) -> raise X_syntax_error
  |Pair(Symbol ("lambda") , Pair(Symbol(_), Nil)) -> raise X_syntax_error
  |Pair(Symbol ("lambda") , Pair(_, Pair(Nil,Nil))) -> raise X_syntax_error
  |Pair(Symbol ("lambda") , Pair(_, Nil)) ->  raise X_syntax_error
  |Pair(Symbol ("lambda") , Pair(Symbol(name), Pair(body,Nil))) ->
     let ok = List.exists (fun (y)-> name = y) reserved_word_list in
     (match ok with
     |true -> raise X_syntax_error
     |false -> LambdaOpt([], name, (tag_parse body)))
  |Pair(Symbol ("lambda") , Pair(Symbol(name), body)) ->
     let ok = List.exists (fun (y)-> name = y) reserved_word_list in
     (match ok with
     |true -> raise X_syntax_error
     |false -> LambdaOpt([], name, Seq(list_of_args body)))

  |Pair(Symbol ("lambda") , Pair(args1, Pair(body,Nil))) -> let ans = (pair_to_list args1) in
                                           (match ans with
                                           |[args;[]] -> LambdaSimple((helper_dup args),(tag_parse body))
                                           |[args;[vs]] ->
                                             let ok = ((List.exists (fun (y)-> vs = y) reserved_word_list) ||
                                                         (List.exists (fun (y)-> vs = y) args))  in
                                                 (match ok with
                                                  |true -> raise X_syntax_error
                                                  |false -> LambdaOpt((helper_dup args),vs, (tag_parse body)))                
                                           |ans -> raise X_syntax_error) 
  |Pair(Symbol ("lambda") , Pair(args1, body)) -> let ans = (pair_to_list args1) in
                                           (match ans with
                                           |[args;[]] -> (match body with
                                                            |Pair(x,Nil)-> LambdaSimple((helper_dup args), (tag_parse x))
                                                            |Pair(_,_)-> LambdaSimple((helper_dup args), Seq(list_of_args body))
                                                            |body -> raise X_syntax_error)
                                           |[args;[vs]] ->
                                             let ok = ((List.exists (fun (y)-> vs = y) reserved_word_list) ||
                                                         (List.exists (fun (y)-> vs = y) args))  in
                                                 (match ok with
                                                  |true -> raise X_syntax_error
                                                  |false -> (match body with
                                                            |Pair(x,Nil)-> LambdaOpt((helper_dup args),vs, (tag_parse x))
                                                            |Pair(_,_)-> LambdaOpt((helper_dup args),vs, Seq(list_of_args body))
                                                            |body -> raise X_syntax_error))
                                           |ans -> raise X_syntax_error)
     
  | Pair(Symbol("or"), Nil)-> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(sexpr,Nil))-> (tag_parse sexpr)
  | Pair(Symbol("or"), body)-> Or((list_of_args body))
  | Pair(Symbol("begin"), Nil)-> Const(Void)
  | Pair(Symbol("begin"), Pair(sexpr,Nil))-> (tag_parse sexpr)
  | Pair(Symbol("begin"), sexprs)-> Seq(list_of_args sexprs)
  | Pair(Symbol("set!"),Pair(Symbol(name), Pair(expr,Nil)))-> Set(Var(name), (tag_parse expr)) 
  | Pair(Symbol("define"), Pair(Symbol(name), Pair(expr,Nil)))->
       let ok = List.exists (fun (y)-> name = y) reserved_word_list in
     (match ok with
     |true -> raise X_syntax_error
     |false -> Def(Var(name), (tag_parse expr)))
     
  | Pair(Symbol("define"), Pair(Pair(Symbol(name),vars),args2))->
        let ok = List.exists (fun (y)-> name = y) reserved_word_list in
     (match ok with
     |true -> raise X_syntax_error
     |false -> Def(Var(name), (tag_parse (Pair(Symbol "lambda",Pair(vars,args2))))))   
  | Pair(Symbol("quasiquote"), Pair(Pair(x1,x2),Nil))-> (match Pair(Pair(x1,x2),Nil)  with
                                     |Pair (Pair (Symbol "unquote", Pair (x, Nil)), Nil) -> (tag_parse x)
                                     |Pair (Pair (Symbol "unquote-splicing", Pair (_, Nil)), Nil) -> raise X_syntax_error
                                     |Pair(x,Nil)-> (match x with      
                                                      |Pair (Pair (Symbol "unquote-splicing",Pair(a,Nil)),b) ->
                                                        Applic(Var("append"),[(tag_parse a);
                                                                             (tag_parse (Pair(Symbol("quasiquote"),Pair(b,Nil))))])
                                                      |Pair (a, (Pair(Symbol "unquote-splicing",Pair(sexpr,Nil)))) ->
                                                         Applic(Var("cons")
                                                               ,[(tag_parse (Pair (Symbol("quasiquote"),Pair(a,Nil))));
                                                                 (tag_parse sexpr)])
                                                      |Pair(a,b)-> Applic(Var("cons")
                                                               ,[(tag_parse (Pair (Symbol("quasiquote"),Pair(a,Nil))));
                                                                 (tag_parse (Pair(Symbol("quasiquote"),Pair(b,Nil))))])
                                                      |x -> raise X_syntax_error)
                                     |z-> raise X_syntax_error)
  |Pair(Symbol "quasiquote",Pair (Vector(exprs),Nil))->  Applic(Var("vector"),List.map (fun(sexpr) ->
                                                                (tag_parse (Pair(Symbol("quasiquote"),Pair(sexpr,Nil))))) exprs)
  |Pair(Symbol("quasiquote"), Pair(sexp,Nil))-> (tag_parse (Pair (Symbol "quote",Pair(sexp,Nil)))) 
  |Pair (Symbol "let" , Pair(args_vals,body)) -> let args = (give_me_args args_vals) in
                                                 let vars = (give_me_vars args_vals) in
                                                 let lambda = Pair(Symbol "lambda",Pair(vars ,body)) in
                                                 Applic((tag_parse lambda),(list_of_args args))
                                   
  |Pair (Symbol "let*" , Pair(Nil,body)) -> (tag_parse (Pair (Symbol "let" , Pair(Nil,body))))
  |Pair (Symbol "let*" , Pair(Pair(Pair(Symbol(x),Pair(exp,Nil)),Nil),body))->
    (tag_parse (Pair (Symbol "let" , Pair(Pair(Pair(Symbol(x),Pair(exp,Nil)),Nil),body))))
  |Pair (Symbol "let*" , Pair(Pair(x,rest),body))->
    (tag_parse (Pair(Symbol "let", Pair(Pair(x,Nil),Pair(Pair(Symbol "let*", Pair(rest,body)),Nil)))))
  |Pair (Symbol "letrec" , Pair(args_vals,body)) ->
                                                    let vars = (give_me_vars_letrec args_vals) in
                                                    let x  = (set_args args_vals body) in
                                                    (match x with
                                                    |Nil-> tag_parse (Pair(Symbol "let",Pair(vars ,body)))
                                                    |x -> tag_parse (Pair(Symbol "let",Pair(vars ,x))))
                                                    
                                                    
                                                                
    |Pair (Symbol "cond" , Pair(Pair(Symbol "else",Pair(y,Nil)),Nil)) ->
      (tag_parse y)
    |Pair (Symbol "cond" , Pair(Pair(Symbol "else",y),Nil)) ->
      Seq(list_of_args y)
    |Pair (Symbol "cond" , Pair(Pair(Symbol "else",_),rest)) ->
      raise X_syntax_error
  
   
    |Pair (Symbol "cond" , Pair(Pair(x,Pair(Symbol "=>", y)),Nil)) ->
   (tag_parse (Pair (Symbol "let",
 Pair
  (Pair
    (Pair (Symbol "value",
      Pair (x, Nil)),
    Pair
     (Pair (Symbol "f",
       Pair (Pair (Symbol "lambda", Pair (Nil, y)), Nil)),
     Nil)),
  Pair
   (Pair (Symbol "if",
     Pair (Symbol "value",
      Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
      Nil))),
    Nil)))))
      |Pair (Symbol "cond" , Pair(Pair(x,Pair(Symbol "=>", y)),rest)) ->
        (tag_parse (Pair (Symbol "let",
  Pair
   (Pair (Pair (Symbol "value", Pair (x, Nil)),
     Pair
      (Pair (Symbol "f",
        Pair (Pair (Symbol "lambda", Pair (Nil, y)),
         Nil)),
      Pair
       (Pair (Symbol "rest",
         Pair
          (Pair (Symbol "lambda",
            Pair (Nil,
             Pair (Pair (Symbol "cond", rest), Nil))),
          Nil)),
       Nil))),
   Pair
    (Pair (Symbol "if",
      Pair (Symbol "value",
       Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
        Pair (Pair (Symbol "rest", Nil), Nil)))),
    Nil)))))

  |Pair (Symbol "cond" , Pair(Pair(x,Pair(y,Nil)),Nil)) ->
    If((tag_parse x) , (tag_parse y)  , Const(Void))
  |Pair (Symbol "cond" , Pair(Pair(x,Pair(y,Nil)),rest)) ->
    If((tag_parse x) , (tag_parse y), (tag_parse (Pair(Symbol "cond" , rest))))
  |Pair (Symbol "cond" , Pair(Pair(x,y),Nil)) ->
    If((tag_parse x) , Seq(list_of_args y), Const(Void))
  |Pair (Symbol "cond" , Pair(Pair(x,y),rest)) ->
    If((tag_parse x) , Seq(list_of_args y), (tag_parse (Pair(Symbol "cond" , rest))))
  |Pair(Symbol "and",Nil) -> Const (Sexpr (Bool(true)))
  |Pair(Symbol "and",Pair(x,Nil))->(tag_parse x)
  |Pair(Symbol "and",Pair(x,rest))->
    If((tag_parse x), (tag_parse (Pair(Symbol "and",rest))),Const (Sexpr (Bool(false))))
  |Pair(x,y) -> Applic((tag_parse x), (list_of_args y))
  |Vector(x)-> Const(Sexpr(Vector(x)))
  


                 

and give_me_vars = function
  |Nil-> Nil
  |Pair(Pair(Symbol(x),Pair(_,Nil)),Nil) -> Pair(Symbol(x),Nil)
  |Pair(Pair(Symbol(x),Pair(_,Nil)),y)-> Pair (Symbol (x), (give_me_vars y))
  |_->raise X_syntax_error

and give_me_vars_letrec = function
  |Nil-> Nil
  |Pair(Pair(Symbol(x),Pair(_,Nil)),Nil) ->
    Pair(Pair(Symbol(x),Pair(Pair(Symbol "quote",Pair(Symbol("whatever"),Nil)),Nil)),Nil) 
  |Pair(Pair(Symbol(x),Pair(_,Nil)),y)->
    Pair(Pair(Symbol(x),Pair(Pair(Symbol "quote",Pair(Symbol("whatever"),Nil)),Nil)),(give_me_vars_letrec y))
  |_->raise X_syntax_error

                                                    
and give_me_args = function
  |Nil->Nil
  |Pair(Pair(Symbol(_),Pair(exp,Nil)),Nil) ->
    Pair(exp, Nil)
  |Pair(Pair(Symbol(_),Pair(exp,Nil)),y)->
    Pair(exp, (give_me_args y))
  |_->raise X_syntax_error

and set_args args body =
  match args with
  |Nil-> Nil
  |Pair(Pair(Symbol(x),Pair(exp,Nil)),Nil) ->
    Pair(Pair(Symbol ("set!"),Pair(Symbol(x), Pair(exp,Nil))),body)
  |Pair(Pair(Symbol(x),Pair(exp,Nil)),y)->
    Pair(Pair(Symbol ("set!"),Pair(Symbol(x), Pair(exp,Nil))),(set_args y body))
  |_->raise X_syntax_error
   
and list_of_args = function
  | Nil-> []
  | Pair(Nil,Nil)->[]
  | Pair(x, Nil)-> [(tag_parse x)]
  | Pair(x , y) -> List.append [(tag_parse x)] (list_of_args y)
  | _ -> raise X_syntax_error
let tag_parse_expression sexpr = (*raise X_syntax_error;;*)
  (tag_parse sexpr);;
let tag_parse_expressions sexpr = (*raise X_syntax_error;;*)
  (List.map (fun (sexp) -> (tag_parse sexp)) sexpr);;

let read exp = Reader.read_sexprs exp;;
end;;


