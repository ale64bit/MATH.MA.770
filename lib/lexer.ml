let digit = [%sedlex.regexp? '0' .. '9']
let number = [%sedlex.regexp? Plus digit]
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let id = [%sedlex.regexp? letter, Plus (letter | number | '_' | '.')]
let str = [%sedlex.regexp? '"', Star any, '"']
let suffix = [%sedlex.regexp? Opt number, Star '\'']
let formula = [%sedlex.regexp? Chars "ABCFG", suffix]
let term = [%sedlex.regexp? Chars "ts", suffix]
let constant = [%sedlex.regexp? 'k', suffix]
let relation = [%sedlex.regexp? 'R', suffix]
let funct = [%sedlex.regexp? Chars "fgh", suffix]
let free_var = [%sedlex.regexp? Chars "abc", suffix]
let bound_var = [%sedlex.regexp? Chars "wxyz", suffix]
let neg = [%sedlex.regexp? "¬" | "~" | "!"]
let disj = [%sedlex.regexp? "∨" | "\\/" | "|"]
let conj = [%sedlex.regexp? "∧" | "/\\" | "&"]
let impl = [%sedlex.regexp? "⊃" | "=>"]
let seq = [%sedlex.regexp? "→" | "->"]
let exists = [%sedlex.regexp? ":E" | "∃"]
let forall = [%sedlex.regexp? ":A" | "∀"]
let turnstile = "⊢"

open Parser

exception Error of string

let rec token buf =
  match%sedlex buf with
  | Plus (Chars " \t") -> token buf
  | '(' -> LPAREN
  | ')' -> RPAREN
  | ',' -> COMMA
  | '/' -> SLASH
  | number -> INT (int_of_string (Sedlexing.Utf8.lexeme buf))
  | str -> STRING (Sedlexing.Utf8.lexeme buf)
  | exists -> EXISTS
  | forall -> FORALL
  | constant -> CONSTANT (Sedlexing.Utf8.lexeme buf)
  | free_var -> FREE_VAR (LK.Free (Sedlexing.Utf8.lexeme buf))
  | bound_var -> BOUND_VAR (LK.Bound (Sedlexing.Utf8.lexeme buf))
  | funct -> FUNCTION (Sedlexing.Utf8.lexeme buf)
  | relation -> RELATION (Sedlexing.Utf8.lexeme buf)
  | formula -> FORMULA (Sedlexing.Utf8.lexeme buf)
  | term -> TERM (Sedlexing.Utf8.lexeme buf)
  | neg -> NEG
  | disj -> DISJ
  | conj -> CONJ
  | impl -> IMPL
  | seq -> SEQ
  | eof -> EOF
  | "axiom" -> AXIOM
  | "premise" -> PREMISE
  | "lweak" -> LWEAK
  | "rweak" -> RWEAK
  | "lcont" -> LCONT
  | "rcont" -> RCONT
  | "lexch" -> LEXCH
  | "rexch" -> REXCH
  | "cut" -> CUT
  | "lneg" -> LNEG
  | "rneg" -> RNEG
  | "llconj" -> LLCONJ
  | "rlconj" -> RLCONJ
  | "rconj" -> RCONJ
  | "ldisj" -> LDISJ
  | "lrdisj" -> LRDISJ
  | "rrdisj" -> RRDISJ
  | "limpl" -> LIMPL
  | "rimpl" -> RIMPL
  | "lforall" -> LFORALL
  | "rforall" -> RFORALL
  | "lexists" -> LEXISTS
  | "rexists" -> REXISTS
  | "macro" -> MACRO
  | "print" -> PRINT
  | "tex" -> TEX
  | "load" -> LOAD
  | "save" -> SAVE
  | "clear" -> CLEAR
  | "mode" -> MODE
  | "LK" -> LK
  | "LJ" -> LJ
  | _ -> raise (Error "unexpected character")
