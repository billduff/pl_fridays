%{
  open! Core
%}

%type <Parse_tree.Exp.t> program
%type <Parse_tree.Typ.t> typ
%type <Parse_tree.Pat.t> pat
%type <Parse_tree.Exp.t> exp

%start program
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE EQUAL BAR DOT COMMA COLON UNDERSCORE ARROW EQARROW PROD SUM REC FUN INJ FOLD MATCH WITH END FIX IS TYPE LET IN EOF
%token <string> Name

%nonassoc IN IS EQARROW
%nonassoc LET FIX FUN
%nonassoc Name LPAREN LBRACE INJ FOLD MATCH
%left ap

%right ARROW

%%

program: exp EOF { $1 }

typ:
  | Name { Var $1 }
  | typ ARROW typ { Arrow ($1, $3) }
  | PROD LBRACKET separated_list(COMMA, labeltype) RBRACKET { Prod $3 }
  | SUM LBRACKET separated_list(COMMA, labeltype) RBRACKET { Sum $3 }
  | REC LBRACKET Name DOT typ RBRACKET { Rec ($3, $5) }

labeltype:
  | Name COLON typ { ($1, $3) }

pat:
  | UNDERSCORE { Wild }
  | Name { Var $1 }
  | LBRACE separated_list(COMMA, recordfield(pat)) RBRACE { Record $2 }
  | INJ LBRACKET Name RBRACKET pat { Inj ($3, $5) }
  | FOLD pat { Fold $2 }
  | LPAREN pat COLON typ RPAREN { Ascribe ($2, $4) }
  | LPAREN pat RPAREN { $2 }

exp:
  | Name { Var $1 }
  | FUN pat EQARROW exp { Fun ($2, $4) }
  | exp exp { Ap ($1, $2) } %prec ap
  | LBRACE separated_list(COMMA, recordfield(exp)) RBRACE { Record $2 }
  | INJ LBRACKET Name RBRACKET exp { Inj ($3, $5) } %prec ap
  | FOLD exp { Fold $2 }
  | MATCH exp WITH BAR? separated_list(BAR, case) END { Match ($2, $5) }
  | FIX Name IS exp { Fix ($2, $4) }
  | LET pat EQUAL exp IN exp { Let (($2, $4), $6) }
  | LET TYPE Name EQUAL typ IN exp { Let_type (($3, $5), $7) }
  | LPAREN exp COLON typ RPAREN { Ascribe ($2, $4) }
  | LPAREN exp RPAREN { $2 }

recordfield(SORT):
  | Name EQUAL SORT { ($1, $3) }

case:
  | pat EQARROW exp { ($1, $3) }
