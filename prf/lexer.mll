{
  open Parser

  exception Error of string
}

let nat = ['0'-'9']+ 
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule line = parse
| ([^'\n']* '\n') as line
    { Some line, true }
| eof
    { None, false }
| ([^'\n']+ as line) eof
    { Some (line ^ "\n"), false }

and token = parse
| [' ' '\t'] { token lexbuf }
| '\n'       { EOL }
| nat        { NAT (Nat.nat_of_int (int_of_string (Lexing.lexeme lexbuf))) }
| id         { ID (Lexing.lexeme lexbuf) }
| '('        { LPAREN }
| ')'        { RPAREN }
| ','        { COMMA }
| '='        { EQ }
| '\''       { SUCC }
| '%'        { COMMENT }
| _          { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }


