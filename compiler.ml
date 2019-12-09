#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;


let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"
(* you can add yours here *)];;

let rec prim_to_pairs_helper offset list =
  match list with
  |((car,body)::cdr)-> List.cons (FVP(car ,offset,body)) (prim_to_pairs_helper (offset + 1) cdr)
  |[]->[];;

let prim_to_pairs fvars =
  let b =  primitive_names_to_labels in
  let a = prim_to_pairs_helper 6 b in
  a;;


  
let get_const_address const =
  let ConstSOB(_,offset,_) = const in
  Printf.sprintf "const_tbl+%d" offset;;
    

let get_fvar_address fvar =
  let FVP(_,offset,_) = fvar in
  Printf.sprintf "fvar_tbl+%d*WORD_SIZE" offset;;

let make_primitive_closure (FVP(_,offset, body)) =
  Printf.sprintf "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, %s) \n mov [fvar_tbl + %d * WORD_SIZE], rax" body offset ;;

let make_constant const =
  let ConstSOB(_,_,s) = const in
  s;;

  
let make_prologue consts_tbl fvars_tbl =
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s

%include \"compiler.s\"
section .bss
malloc_pointer:
    resq 1

section .data
tp: dq 0
format_error_closure: db \"not a closure\",0
format_error_pair: db \"not a pair\",0
apply: MAKE_LITERAL_CLOSURE(apply_body)
car: MAKE_LITERAL_CLOSURE(car_body)
cdr: MAKE_LITERAL_CLOSURE(cdr_body)
cons: MAKE_LITERAL_CLOSURE(cons_body)
set_car: MAKE_LITERAL_CLOSURE(set_car_body)
set_cdr: MAKE_LITERAL_CLOSURE(set_cdr_body)

const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS const_tbl+0
%define SOB_NIL_ADDRESS const_tbl+1
%define SOB_FALSE_ADDRESS const_tbl+2
%define SOB_TRUE_ADDRESS const_tbl+4

fvar_tbl:
dq car
dq cdr
dq cons
dq set_car
dq set_cdr
dq apply
" ^ (String.concat "\n" (List.map (fun(_) -> "dq T_UNDEFINED") fvars_tbl)) ^ "

global main
section .text
main:
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push SOB_NIL_ADDRESS
    push 0
    push qword SOB_NIL_ADDRESS

before:
    call code_fragment
after:
    add rsp, 3*8
    ret

not_closure_error:
 NEW_FRAME
 mov rdi, format_error_closure
 mov rax,0
 call printf
 CLOSE_FRAME

not_pair_error:
 NEW_FRAME
 mov rdi, format_error_pair
 mov rax,0
 call printf
 CLOSE_FRAME

code_fragment:
NEW_FRAME
mov rbx,qword[rbp+16]
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure (prim_to_pairs fvars_tbl))) ^ "
 
";;

let epilogue =
"
apply_body:

   NEW_FRAME
   push SOB_NIL_ADDRESS
   mov r14,PARAM_COUNT; proc + x0,x1 .. + pair element
   mov r13,qword[rbp+8*(3+r14)]; holds the pair
   mov r14,0
   mov r15,SOB_NIL_ADDRESS

.loop_forward:
  cmp r13,SOB_NIL_ADDRESS ; are we done traversing the pair?
  jne .keep_looping_forward
  jmp .pushing_forward

 .keep_looping_forward: 
  add r14,1
  CAR r12,r13 ; r12 holds the car
  MAKE_PAIR(rax,r12,r15); create the reverse pair
  mov r15,rax; save the reveresed on r15
  CDR r13,r13 ; r13 is the cdr now
  jmp .loop_forward
  
.pushing_forward:
   cmp r15,SOB_NIL_ADDRESS; are we done traversing the pair?
   je .push_rest ; if so, push the rest
   CAR r12,r15; save car on r12
   CDR r15,r15; save cdr on r15
   push r12
   jmp .pushing_forward

.push_rest:
    mov r12, PARAM_COUNT
    sub r12,2; x0,x1..
 
.loop_rest:      
    cmp r12,0
    je .change_frame
    mov r13,qword[rbp+8*(4+r12)]
    push r13
    inc r14
    sub r12,1
    jmp .loop_rest


.change_frame:
    push r14
    ;now: all params on stack for the proc. also the number of arguments.
    mov rax, qword[rbp+8*4];proc
    cmp byte[rax], T_CLOSURE
    jne not_closure_error
    push qword[rax+1]
    push qword[rbp+8]
    
    
    mov r8, qword[rbp]
    mov r9, qword[rsp+8*2]
    add r9,4;frame_size
    mov r10, PARAM_COUNT	
    SHIFT_FRAME r9,r10 
    add r10,5
    shl r10,3
    add rsp,r10
    mov rbp,r8


    jmp qword[rax+9]
car_body:
 NEW_FRAME
 mov rax,PVAR(0)
 CAR rax,rax
 CLOSE_FRAME

cdr_body:
 NEW_FRAME
 mov rax,PVAR(0)
 CDR rax,rax
 CLOSE_FRAME

cons_body:
 NEW_FRAME
 mov r12,PVAR(0)
 mov r13,PVAR(1)
 MAKE_PAIR(rax,r12,r13)
 CLOSE_FRAME

set_car_body:
 NEW_FRAME
 mov r12,PVAR(1)
 mov rax,PVAR(0)
 mov qword[rax+1],r12
 mov rax,SOB_VOID_ADDRESS
 CLOSE_FRAME

set_cdr_body:
 NEW_FRAME
 mov r12,PVAR(1)
 mov rax,PVAR(0)
 mov qword[rax+1+WORD_SIZE],r12
 mov rax,SOB_VOID_ADDRESS
 CLOSE_FRAME
";;

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in 
  let code = (file_to_string "stdlib.scm") ^ (file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = (String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void\n " )
                           asts)) ^ "CLOSE_FRAME\n" in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^
                    provided_primitives ^ "\n" ^ epilogue)
 
      
with Invalid_argument(x) -> raise X_missing_input_file;;
