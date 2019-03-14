%{
open Vlog_AST
%}

%token EOF
%token <int * int> Literal
%token <string> Ident
%token <int> Int

%token BangEq
%token PlusColon
%token LtLt
%token LtEq
%token EqEq
%token GtEq
%token GtGt

%token Bang
%token Hash
%token Amp
%token LParen
%token RParen
%token Star
%token Plus
%token Comma
%token Minus
%token Dot
%token Colon
%token Semi
%token Lt
%token Eq
%token Gt
%token Quest
%token At
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%token ALWAYS
%token ASSIGN
%token BEGIN
%token CASE
%token CASEX
%token CASEZ
%token DEFAULT
%token ELSE
%token END
%token ENDCASE
%token ENDMODULE
%token IF
%token INOUT
%token INPUT
%token LOCALPARAM
%token MODULE
%token NEGEDGE
%token OUTPUT
%token PARAMETER
%token POSEDGE
%token REG
%token WIRE

%start <Vlog_AST.module_> top
%type <signal_type> signal_type
%type <signal_decl> signal_decl
%type <instance> instance
%type <always_block> always_block
%type <assign> assign
%type <port_decl> port_decl
%type <decl> decl
%type <expr> expr
%type <proc> proc

(* for resolving if-else conflict *)
%nonassoc RParen
%nonassoc ELSE

(* for resolving port declaration conflict *)

%%

top:
  | MODULE; mod_name = Ident;
    mod_params = loption(preceded(Hash, delimited(LParen, comma_sep_signal_decl_list, RParen)));
    mod_ports = loption(delimited(LParen, comma_sep_port_decl_list, RParen)); Semi;
    mod_decls = list(decl); ENDMODULE; EOF
    {{ mod_name; mod_params; mod_ports; mod_decls }}

(* prevents an unresolvable shift/reduce conflict on Comma *)
comma_sep_signal_decl_list:
  | signal_decl {[$1]}
  | signal_decl_comma comma_sep_signal_decl_list {$1::$2}

port_direction:
  | INPUT  { Input  }
  | OUTPUT { Output }
  | INOUT  { Inout  }

range_spec:
  | LBrack; msb = expr; Colon; lsb = expr; RBrack
    { msb, lsb }

comma_sep_port_decl_list:
  | port_decl {[$1]}
  | port_decl_comma comma_sep_port_decl_list {$1::$2}

port_decl:
  | port_dir = port_direction; port_is_reg = boption(REG);
    port_range_opt = range_spec?;
    port_declarators = separated_nonempty_list(Comma, signal_declarator)
    {{ port_dir; port_is_reg; port_range_opt; port_declarators }}

port_decl_comma:
  | port_dir = port_direction; port_is_reg = boption(REG);
    port_range_opt = range_spec?;
    port_declarators = list(terminated(signal_declarator, Comma))
    {{ port_dir; port_is_reg; port_range_opt; port_declarators }}

assign_lhs:
  | sym = Ident; indices = list(index)
    { E_select (sym, indices) }
  | LBrace; exprs = separated_nonempty_list(Comma, assign_lhs); RBrace
    { E_concat exprs }

index:
  | LBrack; msb = expr; Colon; lsb = expr; RBrack
    { Part_const (msb, lsb) }
  | LBrack; bit = expr; RBrack
    { Bit bit }
  | LBrack; base = expr; PlusColon; width = expr; RBrack
    { Part_var (base, width) }

primary_expr:
  | value = Int
    { E_literal (Literal.make_unsized value) }
  | width = Int; value = Literal
    { E_literal (Literal.make width value) }
  | sym = Ident; indices = list(index)
    { E_select (sym, indices) }
  | LParen; e = expr; RParen {e}
  | LBrace; exprs = separated_nonempty_list(Comma, expr); RBrace
    { E_concat exprs }
  | LBrace; n = expr; LBrace; e = expr; RBrace; RBrace
    { E_duplicate (n, e) }

prefix_op:
  | Tilde { U_not        }
  | Amp   { U_reduce_and }
  | Bar   { U_reduce_or  }

prefix_expr:
  | e = primary_expr {e}
  | op = prefix_op; e = prefix_expr { E_unary (op, e) }

mul_op:
  | Star { B_mul }

mul_expr:
  | e = prefix_expr {e}
  | e1 = mul_expr; op = mul_op; e2 = prefix_expr
    { E_binary (op, e1, e2) }

add_op:
  | Plus  { B_add }
  | Minus { B_sub }

add_expr:
  | e = mul_expr {e}
  | e1 = add_expr; op = add_op; e2 = mul_expr
    { E_binary (op, e1, e2) }

shift_op:
  | LtLt { B_shiftL }
  | GtGt { B_shiftR }

shift_expr:
  | e = add_expr {e}
  | e1 = shift_expr; op = shift_op; e2 = add_expr
    { E_binary (op, e1, e2) }

rel_op:
  | Lt   { B_lt }
  | GtEq { B_ge }
  | Gt   { B_gt }
  | LtEq { B_le }

rel_expr:
  | e = shift_expr {e}
  | e1 = rel_expr; op = rel_op; e2 = shift_expr
    { E_binary (op, e1, e2) }

eq_op:
  | EqEq   { B_eq  }
  | BangEq { B_neq }

eq_expr:
  | e = rel_expr {e}
  | e1 = eq_expr; op = eq_op; e2 = rel_expr
    { E_binary (op, e1, e2) }

and_expr:
  | e = eq_expr {e}
  | e1 = and_expr; Amp; e2 = eq_expr
    { E_binary (B_and, e1, e2) }

xor_expr:
  | e = and_expr {e}
  | e1 = xor_expr; Caret; e2 = and_expr
    { E_binary (B_xor, e1, e2) }

or_expr:
  | e = xor_expr {e}
  | e1 = xor_expr; Bar; e2 = or_expr
    { E_binary (B_or, e1, e2) }

cond_expr:
  | e = or_expr {e}
  | e_cond = or_expr; Quest; e_true = expr; Colon; e_false = expr
    { E_cond (e_cond, e_true, e_false) }

expr:
  | e = cond_expr {e}

assign:
  | ASSIGN; lhs = assign_lhs; Eq; rhs = expr; Semi
    { lhs, rhs }

signal_type:
  | WIRE { Wire }
  | REG  { Reg  }
  | LOCALPARAM { Localparam }
  | PARAMETER  { Parameter  }

signal_declarator:
  | name = Ident; array_dim = list(range_spec);
    eq_expr_opt = preceded(Eq, expr)?
    { name, array_dim, eq_expr_opt }

signal_decl:
  | sig_type = signal_type; sig_range_opt = range_spec?;
    sig_declarators = separated_nonempty_list(Comma, signal_declarator);
    {{ sig_type; sig_range_opt; sig_declarators }}

signal_decl_comma:
  | sig_type = signal_type; sig_range_opt = range_spec?;
    sig_declarators = list(terminated(signal_declarator, Comma));
    {{ sig_type; sig_range_opt; sig_declarators }}

inst_connection:
  | Dot; port_name = Ident; LParen; port_expr_opt = expr?; RParen
    { port_name, port_expr_opt }

instance:
  | inst_class_name = Ident; inst_inst_name = Ident; LParen;
    inst_connections = separated_nonempty_list(Comma, inst_connection);
    RParen; Semi
    {{ inst_class_name; inst_inst_name; inst_connections }}

case_keyword:
  | CASE  { Case  }
  | CASEX { Casex }
  | CASEZ { Casez }

case_expr:
  | DEFAULT { None }
  | e = expr { Some e }

case_branch:
  | expr_opt = case_expr; Colon; proc = proc { expr_opt, proc }

proc:
  | lhs = assign_lhs; Eq; rhs = expr; Semi
    { P_blocking_assign (lhs, rhs) }
  | lhs = assign_lhs; LtEq; rhs = expr; Semi
    { P_nonblocking_assign (lhs, rhs) }
  | BEGIN; procs = list(proc); END
    { P_comp procs }
  | IF; LParen; cond = expr; RParen; proc_t = proc
    { P_if (cond, proc_t, None) }
  | IF; LParen; cond = expr; RParen; proc_t = proc; ELSE; proc_f = proc
    { P_if (cond, proc_t, Some proc_f) }
  | variant = case_keyword; LParen; switch_expr = expr; RParen;
    branches = list(case_branch); ENDCASE
    { P_case (variant, switch_expr, branches) }

sensitivity:
  | Star { Sens_auto }
  | POSEDGE; name = Ident { Sens_posedge name }
  | NEGEDGE; name = Ident { Sens_negedge name }
  | LParen; s = sensitivity; RParen {s}

always_block:
  | ALWAYS; At; sens = sensitivity; proc = proc
    { sens, proc }

decl:
  | decl = signal_decl; Semi
    { Decl_signal decl }
  | decl = assign
    { Decl_assign decl }
  | decl = instance
    { Decl_instance decl }
  | decl = always_block
    { Decl_always decl }
