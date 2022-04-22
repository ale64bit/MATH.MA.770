%token LPAREN RPAREN
%token COMMA EQ SUCC
%token <Nat.t> NAT
%token <string> ID
%token COMMENT EOL

%start <PRF.t> prf_line

%% 

let prf_line :=
  | ~ = prf; EOL; <>

let args == delimited(LPAREN, separated_nonempty_list(COMMA, ID), RPAREN)

let app :=
  | ~ = ID; ~ = args; <>

let vars == separated_nonempty_list(COMMA, ID)

let prf :=
  | ~ = ID; ~ = args; EQ; ~ = ID; SUCC; <PRF.Succ>
  | ~ = ID; ~ = args; EQ; ~ = NAT; <PRF.Const>
  | ~ = ID; ~ = args; EQ; ~ = ID; <PRF.Id>
  | ~ = ID; ~ = args; EQ; ~ = ID; ~ = delimited(LPAREN, separated_nonempty_list(COMMA, app), RPAREN); <PRF.Subs>
  | base_f = ID; LPAREN; base_zero = NAT; RPAREN; EQ; base_q = NAT; COMMA; 
    step_f = ID; LPAREN; step_y_succ = ID; SUCC; RPAREN; EQ; step_xi = ID; LPAREN; step_y = ID; COMMA; step_app = app; RPAREN; 
    {
      PRF.Ind0 {
        ind0_base_f    = base_f;
        ind0_base_zero = base_zero;
        ind0_base_q    = base_q;
        ind0_step_f    = step_f;
        ind0_step_y'   = step_y_succ;
        ind0_step_xi   = step_xi;
        ind0_step_y    = step_y;
        ind0_step_app  = step_app;
      }
    }
  | base_f = ID; LPAREN; base_zero = NAT; COMMA; base_xs = vars; RPAREN; EQ; base_psi = app; COMMA;
    step_f = ID; LPAREN; step_y_succ = ID; SUCC; COMMA; step_xs = vars; RPAREN; EQ; step_xi = ID; LPAREN; step_y = ID; COMMA; step_app = app; COMMA; step_args = vars; RPAREN;
    {
      PRF.Ind1 {
        ind1_base_f    = base_f;
        ind1_base_zero = base_zero;
        ind1_base_xs   = base_xs;
        ind1_base_psi  = base_psi;
        ind1_step_f    = step_f;
        ind1_step_y'   = step_y_succ;
        ind1_step_xs   = step_xs;
        ind1_step_xi   = step_xi;
        ind1_step_y    = step_y;
        ind1_step_app  = step_app;
        ind1_step_args = step_args;
      }
    }

