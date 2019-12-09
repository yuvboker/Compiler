%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_INTEGER 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
%define T_VECTOR 11
%define BACK_SLASH 92	
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
	
%define TYPE_SIZE 1
%define WORD_SIZE 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)

%define TYPE(r) byte[r]
%define DATA(r) [r+TYPE_SIZE]

%define INT_DATA(r) qword DATA(r)
%define FLOAT_DATA(r) qword DATA(r)
%define CHAR_DATA(r) byte DATA(r)
%define BOOL_DATA(r) byte DATA(r)

%define STR_LEN(r) qword DATA(r)
%define STR_DATA_PTR(r) r+WORD_SIZE+TYPE_SIZE
%define STRING_REF(r,i) byte[r+WORD_SIZE+TYPE_SIZE*i]
%macro CLOSURE_ENV 2
 mov %1, qword[%2+TYPE_SIZE]	
%endmacro
%macro CLOSURE_CODE 2
 mov %1, qword[%2+TYPE_SIZE+WORD_SIZE]	
%endmacro

%define CLOSURE_ENV(a,b) mov a, qword[b+TYPE_SIZE+WORD_SIZE]	
%macro MAKE_LITERAL 2
	db %1
	%2
%endmacro

%macro MAKE_LITERAL_S 3
	db %1
	dq %2
	db %3
%endmacro
%define CHAR_BACKSLASH 92
%define MAKE_LITERAL_INT(val) MAKE_LITERAL T_INTEGER, dq val
%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_FLOAT, dq val
%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR, db val
%define MAKE_LITERAL_SYMBOL(val) MAKE_LITERAL T_SYMBOL, dq val
%define MAKE_NIL db T_NIL
%define MAKE_VOID db T_VOID
%define MAKE_BOOL(val) MAKE_LITERAL T_BOOL, db val

%define PARAM_COUNT qword[rbp+3*WORD_SIZE]
%define MAKE_LITERAL_CLOSURE(body)\
	MAKE_WORDS_LIT T_CLOSURE,0,body


%macro NEW_FRAME 0
   push rbp
   mov rbp,rsp
%endmacro


%macro COPY_PARAMS_FROM_STACK 1 
	mov r12,0
	mov r14,0
	mov r13,0
    mov r14,%1
    inc r14
    mov r11,0
    mov r12,qword[rbx]
%%loop2:
    cmp r14,0
    je %%done
    dec r14
    mov r13,qword[rbp+8*(4+r11)]
    mov qword[r12+r11*WORD_SIZE],r13
    inc r11
    jmp %%loop2
%%done:

%endmacro  

%macro EXTEND_ENV 2 ;rbx,r12,depth,PARAM_COUNT
	mov r12,0
	mov r13,0
	mov r14,0
	mov r15,0
	mov rbx,0
   mov r12,qword[rbp+16]
   MALLOC rbx, (%1 + 1) * WORD_SIZE
   mov r15,%2
   inc r15
   shl r15,3
   MALLOC r13, r15
   mov qword[rbx],r13
   mov r14,%1
   mov r11,1
   mov r15,0
%%loop1:
    cmp r14,0
    je %%done
        dec r14
        mov r13,qword[r12+r15*WORD_SIZE]
        mov qword[rbx+r11*WORD_SIZE], r13
        inc r11
        inc r15
    jmp %%loop1
%%done:

%endmacro


%macro CLOSE_FRAME 0
   leave
   ret
%endmacro 

%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro

%macro SKIP_TYPE_TAG_CHAR 2
	push r15
	mov r15,0
	mov r15b, byte [%2+TYPE_SIZE]
	mov %1,	r15
	pop r15
%endmacro		

%define INT_VAL SKIP_TYPE_TAG

%define CHAR_VAL SKIP_TYPE_TAG_CHAR

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG

%define VECTOR_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define VECTOR_ELEMENTS STRING_ELEMENTS

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]
	
%define SOB_UNDEFINED T_UNDEFINED
%define SOB_NIL T_NIL
%define SOB_VOID T_VOID
%define SOB_FALSE word T_BOOL
%define SOB_TRUE word (1 << TYPE_SIZE | T_BOOL)

; returns %2 allocated SIZE in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	push r15
	mov r15,%2
	add qword [malloc_pointer], %2
	mov %1, qword [malloc_pointer]
	sub %1, r15
	pop r15
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_INT(r,val) MAKE_LONG_VALUE r, val, T_INTEGER
%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

%macro MAKE_LITERAL_VECTOR 0-* 
	db T_VECTOR
%rep %0
	dq %1
%rotate 1
%endrep 
%endmacro

%macro MAKE_LITERAL_STRING 0-* 
	db T_STRING
	dq (%%end_str - %%start_str)
%%start_str:
%rep %0
	db %1
%rotate 1
%endrep
%%end_str:
%endmacro


; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

; Create a vector of length %2
; from SOB at %3.
; Stores result in register %1
%macro MAKE_VECTOR 3
	lea %1, [%2*WORD_SIZE+WORD_SIZE+TYPE_SIZE] 
	MALLOC %1, %1
	mov byte [%1], T_VECTOR
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1, WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%vec_loop:
	jz %%vec_loop_end
	dec rcx
	mov qword [%1+rcx*WORD_SIZE], %3
	jmp %%vec_loop
%%vec_loop_end:
	sub %1, WORD_SIZE+TYPE_SIZE
	pop rcx
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro
%define CHANGE(l,num) CHANGE_FRAME l,num

%macro CHANGE_FRAME 2; 1st param: ALL 2nd param: F

	mov rcx,%1;
	sub rcx,%2; R
	mov qword[rsp+16],rcx
	mov r13, SOB_NIL_ADDRESS
	mov rcx,0; counter
	mov r11,%2; F
	mov r12,%1
	add r12,2;
 	
	
%%loop1:
	cmp rcx,r11
	je %%done_change
	mov r10,qword[rsp+8*r12]
	MAKE_PAIR(r14,r10,r13)
	mov r13,r14
	dec r12
	inc rcx
	jmp %%loop1

%%done_change:
	mov qword[rsp+8*(%1+3)],r13 

	mov r11,0; counter
	mov r14,%1;l
	sub r14,%2;l-num
	add r14,3;l-num+3
	
%%loop2:
	cmp r14,r11
	je %%end
	dec r14
	mov r15,r14; 2+l-num
	add r15,%2; 
	mov r10,qword[rsp+8*r14]
	mov qword[rsp+8*r15],r10

	jmp %%loop2
%%end:
	mov r10,%2
	shl r10,3
	add rsp,r10
	
%%final_end:
%endmacro




%macro SHIFT_FRAME 2
        mov r11,0;i
	mov r13, %2
	add r13, 5; 
	mov r12,%1;
%%loop:
	inc r11
	cmp r12,0
	je %%done_change
	mov r15,r11;
	shl r15,3; 8*i
	mov r14,rbp
	sub r14,r15; r14 = rbp-8*i
	mov r15,r14; r15= rbp-8*i
	dec r12
	dec r13
	mov r14, qword[r15]
	mov qword[rbp+WORD_SIZE*r13],r14
	jmp %%loop
%%done_change:
%endmacro

%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

%define FVAR(i) qword[fvar+i*WORD_SIZE]	
extern exit, printf, malloc
global write_sob, write_sob_if_not_void

	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .undefined
	call printf

	leave
	ret

section .data

.undefined:
	db "#<undefined>", 0

write_sob_integer:
	push rbp
	mov rbp, rsp

	INT_VAL rsi, rsi
	mov rdi, .int_format_string
	mov rax, 0
	call printf

	leave
	ret

section .data
.int_format_string:
	db "%ld", 0

write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	mov rsi, rsp
	and rsp, -16
	call printf
	mov rsp, rsi

	leave
	ret
	
section .data
.float_format_string:
	db "%f", 0		

write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	leave
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	leave
	ret

section .data
.void:
	db "#<void>", 0
	
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], SOB_FALSE
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	leave
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	leave
	ret

section .data
.nil:
	db "()", 0

write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	leave
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]
    
	CAR rsi,rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi,rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	leave
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

	add rsp, 1*8

.done:
	leave
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

write_sob_vector:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .fs_open_vector ; "#(
	call printf

	pop rsi

	VECTOR_LENGTH rcx, rsi; rcx = length
	cmp rcx, 0
	je .done
	VECTOR_ELEMENTS rax, rsi; rax-pointer to the first element

	push rcx
	push rax
	mov rsi, qword [rax]
	call write_sob
	pop rax
	pop rcx
	dec rcx
	add rax, 8

.loop:
	cmp rcx, 0
	je .done

	push rcx
	push rax
	mov rax, 0
	mov rdi, .fs_space
	call printf
	
	pop rax
	push rax
	mov rsi, qword [rax]
	call write_sob
	pop rax
	pop rcx
	dec rcx
	add rax, 8
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .fs_close_vector
	call printf

	leave
	ret

section	.data
.fs_open_vector:
	db "#(", 0
.fs_close_vector:
	db ")", 0
.fs_space:
	db " ", 0

write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	leave
	ret

section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	leave
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_integer, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair, write_sob_vector

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte[rax]
	cmp bl, SOB_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0
