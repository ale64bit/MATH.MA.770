%token <int> INT
%token <string> STRING
%token <string> CONSTANT
%token <LK.var> BOUND_VAR
%token <LK.var> FREE_VAR
%token <string> FUNCTION
%token <string> RELATION
%token <string> FORMULA
%token <string> TERM
%token LPAREN RPAREN
%token SEQ
%token IMPL
%token NEG DISJ CONJ
%token EXISTS FORALL
%token COMMA
%token SLASH
%token MACRO
%token EOF

(* Commands *)
%token AXIOM PREMISE
%token LWEAK RWEAK 
%token LCONT RCONT
%token LEXCH REXCH
%token CUT
%token LNEG RNEG
%token LLCONJ RLCONJ RCONJ
%token LDISJ LRDISJ RRDISJ
%token LIMPL RIMPL
%token LFORALL RFORALL
%token LEXISTS REXISTS
%token PRINT
%token TEX
%token LOAD SAVE
%token CLEAR
%token MODE LK LJ

(* Precedence *)
%right IMPL 
%right DISJ CONJ
%right NEG 
%right EXISTS FORALL

%start <LK.sequent> start_sequent
%start <LK.formula> start_formula
%start <LK.term> start_term
%start <Cmd.cmd> start_cmd

%%

let start_sequent :=
  | ~ = sequent; EOF; <>

let start_term :=
  | ~ = term; EOF; <>

let start_formula :=
  | ~ = formula; EOF; <>

let start_cmd :=
  | ~ = cmd; EOF; <>

let var :=
  | ~ = FREE_VAR; <>
  | ~ = BOUND_VAR; <>

let term :=
  | ~ = CONSTANT; <LK.Const>
  | ~ = FREE_VAR; <LK.Var>
  | ~ = FUNCTION; ~ = loption(delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)); <LK.Fun>
  | ~ = TERM; ~ = loption(delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)); <LK.Term>

let semiterm :=
  | ~ = CONSTANT; <LK.Const>
  | ~ = var; <LK.Var>
  | ~ = FUNCTION; ~ = loption(delimited(LPAREN, separated_nonempty_list(COMMA, semiterm), RPAREN)); <LK.Fun>
  | ~ = TERM; ~ = loption(delimited(LPAREN, separated_nonempty_list(COMMA, semiterm), RPAREN)); <LK.Term>

let formula :=
  | ~ = RELATION; ~ = delimited(LPAREN, separated_nonempty_list(COMMA, semiterm), RPAREN); <LK.Atom>
  | NEG; ~ = formula; <LK.Neg>
  | a = formula; DISJ; b = formula; { LK.Disj (a, b) }
  | a = formula; CONJ; b = formula; { LK.Conj (a, b) }
  | a = formula; IMPL; b = formula; { LK.Impl (a, b) }
  | EXISTS; ~ = BOUND_VAR; ~ = formula; <LK.Exists> %prec EXISTS
  | FORALL; ~ = BOUND_VAR; ~ = formula; <LK.ForAll> %prec FORALL
  | ~ = FORMULA; ~ = loption(delimited(LPAREN, separated_nonempty_list(COMMA, semiterm), RPAREN)); <LK.Formula>
  | ~ = delimited(LPAREN, formula, RPAREN); <>

let sequent :=
  ~ = separated_list(COMMA, formula); SEQ; ~ = separated_list(COMMA, formula); EOF; <>

let replacement :=
  f = formula; SLASH; g = formula; { (f, g) }

let cmd :=
  | AXIOM; ~ = formula; <Cmd.Axiom>
  | PREMISE; ~ = sequent; <Cmd.Premise>
  | LWEAK; index = INT; d = formula; { Cmd.Weakening (LK.Left, index, d) } 
  | RWEAK; index = INT; d = formula; { Cmd.Weakening (LK.Right, index, d) } 
  | LCONT; index = INT; { Cmd.Contraction (LK.Left, index) } 
  | RCONT; index = INT; { Cmd.Contraction (LK.Right, index) } 
  | LEXCH; index = INT; start = INT; { Cmd.Exchange (LK.Left, index, start) }
  | REXCH; index = INT; start = INT; { Cmd.Exchange (LK.Right, index, start) }
  | CUT; ~ = INT; ~ = INT; <Cmd.Cut>
  | LNEG; index = INT; { Cmd.Negation (LK.Left, index) } 
  | RNEG; index = INT; { Cmd.Negation (LK.Right, index) } 
  | LLCONJ; index = INT; d = formula; { Cmd.ConjLeft (LK.Left, index, d) }
  | RLCONJ; index = INT; d = formula; { Cmd.ConjLeft (LK.Right, index, d) }
  | RCONJ; ~ = INT; ~ = INT; <Cmd.ConjRight>
  | LDISJ; ~ = INT; ~ = INT; <Cmd.DisjLeft>
  | LRDISJ; index = INT; d = formula; { Cmd.DisjRight (LK.Left, index, d) }
  | RRDISJ; index = INT; d = formula; { Cmd.DisjRight (LK.Right, index, d) }
  | LIMPL; ~ = INT; ~ = INT; <Cmd.ImplLeft>
  | RIMPL; ~ = INT; <Cmd.ImplRight>
  | LFORALL; ~ = INT; ~ = term; ~ = BOUND_VAR; <Cmd.ForAllLeft>
  | RFORALL; ~ = INT; ~ = FREE_VAR; ~ = BOUND_VAR; <Cmd.ForAllRight>
  | LEXISTS; ~ = INT; ~ = FREE_VAR; ~ = BOUND_VAR; <Cmd.ExistsLeft>
  | REXISTS; ~ = INT; ~ = term; ~ = BOUND_VAR; <Cmd.ExistsRight>
  | MACRO; path = STRING; repl = separated_list(COMMA, replacement); { Cmd.Macro (path, repl) }
  | PRINT; { Cmd.Print }
  | TEX; ~ = STRING; <Cmd.TeX>
  | LOAD; ~ = STRING; <Cmd.Load>
  | SAVE; ~ = STRING; <Cmd.Save>
  | CLEAR; { Cmd.Clear }
  | MODE; LK; { Cmd.Mode Cmd.Classic }
  | MODE; LJ; { Cmd.Mode Cmd.Intuitionistic }
