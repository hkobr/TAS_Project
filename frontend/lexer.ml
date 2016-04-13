# 11 "frontend/lexer.mll"
 
open Lexing
open Abstract_syntax_tree
open Parser

(* keyword table *)
let kwd_table = Hashtbl.create 10
let _ = 
  List.iter (fun (a,b) -> Hashtbl.add kwd_table a b)
    [
     (* types *)
     "int",    TOK_INT;
     
     (* constants *)
     "true",   TOK_TRUE; 
     "false",  TOK_FALSE;

     (* expression operators *)
     "rand",   TOK_RAND;

     (* control flow *)
     "while",  TOK_WHILE;
     "if",     TOK_IF;
     "else",   TOK_ELSE;
     "halt",   TOK_HALT;

     (* special statements *)
     "assert", TOK_ASSERT;
     "print",  TOK_PRINT;
   ]

# 34 "frontend/lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\228\255\002\000\007\000\230\255\078\000\088\000\234\255\
    \236\255\237\255\022\000\008\000\002\000\003\000\030\000\105\000\
    \031\000\248\255\249\255\250\255\251\255\252\255\253\255\254\255\
    \162\000\240\255\083\000\232\255\243\255\242\255\241\255\239\255\
    \238\255\243\000\107\000\100\000\102\000\010\001\025\001\153\000\
    \002\000\253\255\254\255\011\000\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\026\000\025\000\255\255\022\000\022\000\255\255\
    \255\255\255\255\255\255\255\255\020\000\011\000\010\000\009\000\
    \008\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\024\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\022\000\022\000\022\000\255\255\
    \002\000\255\255\255\255\001\000\255\255";
  Lexing.lex_default = 
   "\255\255\000\000\255\255\255\255\000\000\255\255\255\255\000\000\
    \000\000\000\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\026\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\042\000\
    \255\255\000\000\000\000\255\255\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\002\000\004\000\002\000\041\000\003\000\000\000\002\000\
    \002\000\004\000\000\000\000\000\002\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\016\000\002\000\000\000\000\000\007\000\011\000\002\000\
    \023\000\022\000\019\000\018\000\008\000\017\000\031\000\015\000\
    \006\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\044\000\009\000\014\000\012\000\013\000\030\000\
    \029\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\028\000\025\000\255\255\000\000\024\000\
    \255\255\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\021\000\010\000\020\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\032\000\027\000\036\000\036\000\036\000\036\000\
    \026\000\000\000\035\000\037\000\037\000\037\000\037\000\037\000\
    \037\000\037\000\037\000\041\000\000\000\000\000\040\000\034\000\
    \000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\
    \033\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
    \000\000\000\000\035\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\043\000\000\000\036\000\000\000\034\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \033\000\000\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\000\000\000\000\000\000\
    \001\000\024\000\000\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\037\000\037\000\037\000\037\000\037\000\037\000\
    \037\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\255\255\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \038\000\000\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\002\000\040\000\000\000\255\255\002\000\
    \003\000\003\000\255\255\255\255\003\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\002\000\255\255\255\255\000\000\000\000\003\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\011\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\043\000\000\000\000\000\000\000\000\000\012\000\
    \013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\014\000\016\000\026\000\255\255\000\000\
    \026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\010\000\015\000\035\000\035\000\036\000\036\000\
    \015\000\255\255\006\000\034\000\034\000\034\000\034\000\034\000\
    \034\000\034\000\034\000\039\000\255\255\255\255\039\000\006\000\
    \255\255\255\255\255\255\255\255\255\255\005\000\255\255\255\255\
    \006\000\255\255\255\255\255\255\255\255\255\255\255\255\006\000\
    \255\255\255\255\006\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\039\000\255\255\036\000\255\255\006\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \006\000\255\255\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\255\255\255\255\255\255\
    \000\000\024\000\255\255\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\033\000\033\000\033\000\033\000\033\000\
    \033\000\033\000\033\000\033\000\033\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\033\000\033\000\033\000\033\000\
    \033\000\033\000\037\000\037\000\037\000\037\000\037\000\037\000\
    \037\000\037\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\026\000\033\000\033\000\033\000\033\000\
    \033\000\033\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\037\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \038\000\255\255\038\000\038\000\038\000\038\000\038\000\038\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\039\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec token lexbuf =
    __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 63 "frontend/lexer.mll"
                                                          id
# 217 "frontend/lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 64 "frontend/lexer.mll"
( try Hashtbl.find kwd_table id with Not_found -> TOK_id id )
# 221 "frontend/lexer.ml"

  | 1 ->
# 67 "frontend/lexer.mll"
         ( TOK_LPAREN )
# 226 "frontend/lexer.ml"

  | 2 ->
# 68 "frontend/lexer.mll"
         ( TOK_RPAREN )
# 231 "frontend/lexer.ml"

  | 3 ->
# 69 "frontend/lexer.mll"
         ( TOK_LCURLY )
# 236 "frontend/lexer.ml"

  | 4 ->
# 70 "frontend/lexer.mll"
         ( TOK_RCURLY )
# 241 "frontend/lexer.ml"

  | 5 ->
# 71 "frontend/lexer.mll"
         ( TOK_STAR )
# 246 "frontend/lexer.ml"

  | 6 ->
# 72 "frontend/lexer.mll"
         ( TOK_PLUS )
# 251 "frontend/lexer.ml"

  | 7 ->
# 73 "frontend/lexer.mll"
         ( TOK_MINUS )
# 256 "frontend/lexer.ml"

  | 8 ->
# 74 "frontend/lexer.mll"
         ( TOK_EXCLAIM )
# 261 "frontend/lexer.ml"

  | 9 ->
# 75 "frontend/lexer.mll"
         ( TOK_DIVIDE )
# 266 "frontend/lexer.ml"

  | 10 ->
# 76 "frontend/lexer.mll"
         ( TOK_LESS )
# 271 "frontend/lexer.ml"

  | 11 ->
# 77 "frontend/lexer.mll"
         ( TOK_GREATER )
# 276 "frontend/lexer.ml"

  | 12 ->
# 78 "frontend/lexer.mll"
         ( TOK_LESS_EQUAL )
# 281 "frontend/lexer.ml"

  | 13 ->
# 79 "frontend/lexer.mll"
         ( TOK_GREATER_EQUAL )
# 286 "frontend/lexer.ml"

  | 14 ->
# 80 "frontend/lexer.mll"
         ( TOK_EQUAL_EQUAL )
# 291 "frontend/lexer.ml"

  | 15 ->
# 81 "frontend/lexer.mll"
         ( TOK_NOT_EQUAL )
# 296 "frontend/lexer.ml"

  | 16 ->
# 82 "frontend/lexer.mll"
         ( TOK_AND_AND )
# 301 "frontend/lexer.ml"

  | 17 ->
# 83 "frontend/lexer.mll"
         ( TOK_BAR_BAR )
# 306 "frontend/lexer.ml"

  | 18 ->
# 84 "frontend/lexer.mll"
         ( TOK_SEMICOLON )
# 311 "frontend/lexer.ml"

  | 19 ->
# 85 "frontend/lexer.mll"
         ( TOK_COMMA )
# 316 "frontend/lexer.ml"

  | 20 ->
# 86 "frontend/lexer.mll"
         ( TOK_EQUAL )
# 321 "frontend/lexer.ml"

  | 21 ->
# 87 "frontend/lexer.mll"
       ( TOK_MODULO )
# 326 "frontend/lexer.ml"

  | 22 ->
let
# 90 "frontend/lexer.mll"
                  c
# 332 "frontend/lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 90 "frontend/lexer.mll"
                    ( TOK_int c )
# 336 "frontend/lexer.ml"

  | 23 ->
# 93 "frontend/lexer.mll"
       ( comment lexbuf; token lexbuf )
# 341 "frontend/lexer.ml"

  | 24 ->
# 94 "frontend/lexer.mll"
                      ( token lexbuf )
# 346 "frontend/lexer.ml"

  | 25 ->
# 95 "frontend/lexer.mll"
          ( new_line lexbuf; token lexbuf )
# 351 "frontend/lexer.ml"

  | 26 ->
# 96 "frontend/lexer.mll"
        ( token lexbuf )
# 356 "frontend/lexer.ml"

  | 27 ->
# 99 "frontend/lexer.mll"
      ( TOK_EOF )
# 361 "frontend/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 39
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 104 "frontend/lexer.mll"
       ( () )
# 372 "frontend/lexer.ml"

  | 1 ->
# 105 "frontend/lexer.mll"
                ( comment lexbuf )
# 377 "frontend/lexer.ml"

  | 2 ->
# 106 "frontend/lexer.mll"
          ( new_line lexbuf; comment lexbuf )
# 382 "frontend/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;
