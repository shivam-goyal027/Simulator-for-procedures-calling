#directory "_build";; (* Consider this folder when looking for files *)
#load "expression.cmo";;
#load "parser.cmo";;
#load "lexer.cmo";;

open Parser;;
open Expression;;
open Lexer;;

exception Not_implemented

let exp_parser s = Parser.main Lexer.token (Lexing.from_string s) ;;

let t="call P(w,2)";;
let p=exp_parser t;;


