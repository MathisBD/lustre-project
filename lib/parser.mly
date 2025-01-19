%{
  open Asttypes
  open Ast

  let mk_expr e loc = { pexpr_desc = e; pexpr_loc = loc }
  let mk_patt p loc = { ppatt_desc = p; ppatt_loc = loc }
%}

%token AND
%token BOOL  
%token CONST
%token COLON
%token COMMA
%token <Asttypes.binop> COMP
%token <bool> CONST_BOOL
%token <int> CONST_INT
%token <float> CONST_FLOAT
%token <string> CONST_STRING
%token ELSE
%token END
%token EOF
%token EQUAL
%token NEQ
%token PRE
%token ARROW
%token FLOAT 
%token <string> IDENT
%token IF
%token INT   
%token LET
%token LPAREN
%token MINUS
%token MINUS_DOT
%token NODE
%token NOT
%token OR
%token PLUS
%token PLUS_DOT
%token RETURNS
%token RPAREN
%token SEMICOL
%token SLASH
%token SLASH_DOT
%token STAR
%token STAR_DOT
%token STRING
%token TEL
%token THEN
%token UNIT  
%token VAR

%nonassoc THEN
%nonassoc ELSE
%right ARROW
%left OR 
%left AND
%left COMP EQUAL NEQ                          /* < <= > >= <> = <> */
%left PLUS MINUS PLUS_DOT MINUS_DOT           /* + -  */
%left STAR SLASH STAR_DOT SLASH_DOT           /* * /  */
%nonassoc uminus                              /* - */
%nonassoc NOT                                 /* not */
%nonassoc PRE
%left DOT

/* Point d'entrée */

%start file
%type <Ast.p_file> file

%%

file: node_decs EOF { $1 }
;

node_decs:
| /* empty */       { [] }
| node node_decs    { $1 :: $2 }
;


node:
| NODE IDENT LPAREN in_params RPAREN 
  RETURNS LPAREN out_params RPAREN SEMICOL
  local_params 
  LET eq_list TEL
    { { pn_name = $2
	  ; pn_input = $4
	  ; pn_output = $8
	  ; pn_local = $11
	  ; pn_equs = $13
	  ; pn_loc = ($startpos, $endpos) } }
;

in_params:
| /* empty */
    { [] }
| param_list
    { $1 }
;


out_params:
| param_list
    { $1 }
;

local_params:
| /* empty */
    { [] }
| VAR param_list_semicol
    { $2 }
;

param_list:
| param 
    { $1 }
| param SEMICOL param_list
    { $1 @ $3 }
;

param_list_semicol:
| param  SEMICOL
    { $1 }
| param SEMICOL param_list_semicol
    { $1 @ $3 }
;


param:
  | ident_comma_list COLON typ
      { let typ = $3 in
        List.map (fun id -> (id, typ)) $1 }
;

eq_list:
| eq
    { [$1] }
| eq eq_list
    { $1 :: $2 }
;

eq:
| pattern EQUAL expr SEMICOL
    { { peq_patt = $1; peq_expr = $3; } }
;

pattern:
| IDENT
    { mk_patt (PP_ident $1) ($startpos, $endpos) }
| LPAREN IDENT COMMA ident_comma_list RPAREN
    { mk_patt (PP_tuple($2::$4)) ($startpos, $endpos) }
;

expr:
| LPAREN expr RPAREN
    { $2 }
| const 
    { $1 }
| IDENT 
    { mk_expr (PE_ident $1) ($startpos, $endpos) }
| IDENT LPAREN expr_comma_list_empty RPAREN
    { mk_expr (PE_app ($1, $3)) ($startpos, $endpos) }
| IF expr THEN expr ELSE expr
    { mk_expr (PE_if ($2, $4, $6)) ($startpos, $endpos) }
| PRE expr
    { mk_expr (PE_pre $2) ($startpos, $endpos) }
| expr ARROW expr
    { mk_expr (PE_arrow ($1, $3)) ($startpos, $endpos) }
| expr PLUS expr          
    { mk_expr (PE_binop (Badd, $1, $3)) ($startpos, $endpos) }
| expr PLUS_DOT expr          
    { mk_expr (PE_binop (Badd_f, $1, $3)) ($startpos, $endpos) }
| expr MINUS expr         
    { mk_expr (PE_binop (Bsub, $1, $3)) ($startpos, $endpos) }
| expr MINUS_DOT expr         
    { mk_expr (PE_binop (Bsub_f, $1, $3)) ($startpos, $endpos) }
| expr STAR expr        
    { mk_expr (PE_binop (Bmul, $1, $3)) ($startpos, $endpos) }
| expr STAR_DOT expr        
    { mk_expr (PE_binop (Bmul_f, $1, $3)) ($startpos, $endpos) }
| expr SLASH expr        
    { mk_expr (PE_binop (Bdiv, $1, $3)) ($startpos, $endpos) }
| expr SLASH_DOT expr        
    { mk_expr (PE_binop (Bdiv_f, $1, $3)) ($startpos, $endpos) }
| expr COMP expr         
    { mk_expr (PE_binop ($2, $1, $3)) ($startpos, $endpos) }
| expr EQUAL expr         
    { mk_expr (PE_binop (Beq, $1, $3)) ($startpos, $endpos) }
| expr NEQ expr         
    { mk_expr (PE_binop (Bneq, $1, $3)) ($startpos, $endpos) }
| expr AND expr          
    { mk_expr (PE_binop (Band, $1, $3)) ($startpos, $endpos) }
| expr OR expr          
    { mk_expr (PE_binop (Bor, $1, $3)) ($startpos, $endpos) }
| MINUS expr /* %prec uminus */
    { mk_expr (PE_unop (Uminus, $2)) ($startpos, $endpos) }
| MINUS_DOT expr /* %prec uminus */
    { mk_expr (PE_unop (Uminus_f, $2)) ($startpos, $endpos) }
| NOT expr
    { mk_expr (PE_unop (Unot, $2)) ($startpos, $endpos) }
| LPAREN expr COMMA expr_comma_list RPAREN
    { mk_expr (PE_tuple ($2::$4)) ($startpos, $endpos) }
;

const:
| LPAREN RPAREN
    { mk_expr (PE_const Cunit) ($startpos, $endpos) }
| CONST_BOOL 
    { mk_expr (PE_const (Cbool $1)) ($startpos, $endpos) }
| CONST_INT 
    { mk_expr (PE_const (Cint $1)) ($startpos, $endpos) }
| CONST_FLOAT
    { mk_expr (PE_const (Cfloat $1)) ($startpos, $endpos) }
| CONST_STRING 
    { mk_expr (PE_const (Cstring $1)) ($startpos, $endpos) }
;

ident_comma_list:
| IDENT COMMA ident_comma_list
    { $1 :: $3 }
| IDENT { [$1] }
;

expr_comma_list_empty:
    { [] }
| expr_comma_list { $1 }
;

expr_comma_list:
| expr COMMA expr_comma_list
    { $1 :: $3 }
| expr { [$1] }
;

typ:
| UNIT   { Tunit }
| BOOL   { Tbool }
| INT    { Tint }
| FLOAT  { Tfloat }
| STRING { Tstring }
;
