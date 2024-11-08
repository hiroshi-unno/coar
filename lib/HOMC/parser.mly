%{
open Ast

let print_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  print_string ("File \"" ^ st.Lexing.pos_fname);
  Format.printf "\", line %d" st.Lexing.pos_lnum;
  Format.printf ", characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)

let coerce_idx = ref 1
%}

%token BEGING ENDG
%token BEGINA ENDA
%token BEGINR ENDR
%token BEGINATA ENDATA
%token BEGINT ENDT

/*%token FAIL*/
%token CASE OF BAR COERCE COPY GEN
%token TRUE FALSE AND OR
%token <string> LIDENT
%token <string> UIDENT
%token <int> INT

%token PERIOD COMMA COLON
%token EQUAL MINUS_RANGLE EQUAL_RANGLE
%token LPAREN RPAREN
%token EOF

%left OR
%left AND

%type <EHMTT.t * Automata.TreeAutomaton.t> hors
%type <EHMTT.t * Automata.TTA.pre_trs * (Ident.tvar * Ident.tvar RefType.t)> hmtt
%type <EHMTT.t> rules
%type <Automata.TreeAutomaton.t> tree_automata
%type <Automata.TTA.pre_trs> tta_transitions
%type <(Ident.tvar * Ident.tvar RefType.t) list> typedefs
%start hors hmtt rules tree_automata tta_transitions typedefs

%%

hors:
  BEGING rules ENDG tree_automata EOF
    { $2, $4 }
| error
    { print_error_information ();
      raise (Failure "Syntax error") }

hmtt:
  BEGING rules ENDG BEGINA tta_transitions ENDA BEGINT typedef ENDT EOF
    { $2, $5, $8 }
| error
    { print_error_information ();
      raise (Failure "Syntax error") }

tree_automata:
  BEGINA tta_transitions ENDA
    { Automata.TreeAutomaton.TTA (Automata.TTA.make $2) }
| BEGINR ata_arities ENDR BEGINATA ata_transitions ENDATA
    { Automata.TreeAutomaton.ATA ($2, Automata.ATA.make $5) }
| error
    { print_error_information ();
      raise (Failure "Syntax error") }

rules:
  /* empty */
    { [] }
| rule rules
    { $1::$2 }
| EOF
    { [] }

rule:
  UIDENT lidents MINUS_RANGLE term PERIOD
    { Ident.Tvar $1, ($2, EHMTT.elimVarOrTerm $2 $4) }
| UIDENT lidents EQUAL term PERIOD
    { Ident.Tvar $1, ($2, EHMTT.elimVarOrTerm $2 $4) }

simple_term:
  LPAREN term RPAREN
    { $2 }
| LIDENT
    { EHMTT.VarOrTerm(Ident.Tvar $1) }
| UIDENT
    { EHMTT.Nonterm(Ident.Tvar $1) }
| INT
    { EHMTT.Fd $1 }

term:
  simple_term
    { $1 }
| term simple_term
    { EHMTT.App($1, $2) }
| CASE LIDENT OF pats
    { EHMTT.Case(Ident.Tvar $2, $4) }
| COERCE LIDENT simple_term
    { 
      let idx = !coerce_idx in
      coerce_idx := idx + 1;
      EHMTT.Coerce(Ident.Tvar $2, $3, idx) 
    }
| COPY simple_term
    { EHMTT.Copy($2) }
| GEN LIDENT
    { EHMTT.Tree(Ident.Tvar $2) }

pats:
  pat
    { [$1] }
| pat BAR pats
    { $1::$3 }

pat:
  LIDENT lidents EQUAL_RANGLE term
    { Ident.Tvar $1, ($2, $4) }

lidents:
  /* empty */
    { [] }
| LIDENT lidents
    { (Ident.Tvar $1) :: $2 }

tta_transitions:
  /* empty */
    { [] }
| LIDENT LIDENT MINUS_RANGLE lidents PERIOD tta_transitions
    { ($1, ($2, List.map Ident.name_of_tvar $4)) :: $6 }
| EOF
    { [] }

ata_arities:
  /* empty */
    { [] }
| LIDENT MINUS_RANGLE INT PERIOD ata_arities
    { ($1, $3) :: $5 }
| EOF
    { [] }

ata_transitions:
  /* empty */
    { [] }
| LIDENT LIDENT MINUS_RANGLE dnf PERIOD ata_transitions
    { ($1, ($2, $4)) :: $6 }
| EOF
    { [] }

dnf:
  FALSE { [] }
| cube { [$1] }
| cube OR dnf { $1 :: $3 }

cube:
  TRUE { [] }
| LPAREN INT COMMA LIDENT RPAREN { [($2, $4)] }
| LPAREN INT COMMA LIDENT RPAREN AND cube { ($2, $4) :: $7 }


typedefs:
  /* empty */
    { [] }
| typedef typedefs
    { $1::$2 }
| EOF
    { [] }

typedef:
  UIDENT COLON typ PERIOD
    { Ident.Tvar $1, $3 }
| LIDENT COLON typ PERIOD
    { Ident.Tvar $1, $3 }

typ:
  LIDENT
    { RefType.Base(Ident.Tvar $1) }
| typ MINUS_RANGLE typ
    { RefType.Func($1, $3) }
| LPAREN typ RPAREN
    { $2 }
