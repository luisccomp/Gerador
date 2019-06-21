
(* The type of tokens. *)

type token = 
  | WHILE of (Lexing.position)
  | VOID of (Lexing.position)
  | VIRG of (Lexing.position)
  | VEZESIGUAL of (Lexing.position)
  | VEZES of (Lexing.position)
  | SWITCH of (Lexing.position)
  | STRING of (Lexing.position)
  | STATIC of (Lexing.position)
  | RETURN of (Lexing.position)
  | READSTRING of (Lexing.position)
  | READINT of (Lexing.position)
  | READFLOAT of (Lexing.position)
  | READCHAR of (Lexing.position)
  | PUBLIC of (Lexing.position)
  | PTV of (Lexing.position)
  | PTO of (Lexing.position)
  | PRINT of (Lexing.position)
  | OULOG of (Lexing.position)
  | NOT of (Lexing.position)
  | MOD of (Lexing.position)
  | MENOSMENOS of (Lexing.position)
  | MENOSIGUAL of (Lexing.position)
  | MENOS of (Lexing.position)
  | MENORIGUAL of (Lexing.position)
  | MENOR of (Lexing.position)
  | MAISMAIS of (Lexing.position)
  | MAISIGUAL of (Lexing.position)
  | MAIS of (Lexing.position)
  | MAIORIGUAL of (Lexing.position)
  | MAIOR of (Lexing.position)
  | MAIN of (Lexing.position)
  | LITSTRING of (string * Lexing.position)
  | LITINT of (int * Lexing.position)
  | LITFLOAT of (float * Lexing.position)
  | LITCHAR of (char * Lexing.position)
  | LITBOOL of (bool * Lexing.position)
  | INT of (Lexing.position)
  | IGUAL of (Lexing.position)
  | IF of (Lexing.position)
  | ID of (string * Lexing.position)
  | FPAR of (Lexing.position)
  | FOR of (Lexing.position)
  | FLOAT of (Lexing.position)
  | FCOL of (Lexing.position)
  | FCHAVE of (Lexing.position)
  | EOF
  | ELSE of (Lexing.position)
  | ELOG of (Lexing.position)
  | DPTOS of (Lexing.position)
  | DIVIGUAL of (Lexing.position)
  | DIV of (Lexing.position)
  | DIFER of (Lexing.position)
  | DEFAULT of (Lexing.position)
  | CLASS of (Lexing.position)
  | CHAR of (Lexing.position)
  | CASE of (Lexing.position)
  | BREAK of (Lexing.position)
  | BOOLEAN of (Lexing.position)
  | ATRIB of (Lexing.position)
  | ARGV of (Lexing.position)
  | APAR of (Lexing.position)
  | ACOL of (Lexing.position)
  | ACHAVE of (Lexing.position)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val programa: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Sast.expressao Ast.programa)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val programa: Lexing.position -> (Sast.expressao Ast.programa) MenhirInterpreter.checkpoint
  
end
