type token =
  | LP
  | RP
  | COLON
  | EQUAL
  | CALL
  | RET
  | EOL
  | EOF
  | COMMA
  | INT of (int)
  | VAR of (string)
  | FUNC of (string)

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Expression.expr_tree
