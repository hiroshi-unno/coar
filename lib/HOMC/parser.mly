%{
open Ast

let coerce_idx = ref 1
%}

%token BEGING ENDG
%token BEGINA ENDA
%token BEGINR ENDR
%token BEGINATA ENDATA
%token BEGINT ENDT
/* the text of a [%BEGINX ... %ENDX] section and the position it begins at */
%token <string * Lexing.position> XTYPES

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

/* `->` is right-associative: `a -> b -> c` parses as `a -> (b -> c)`.
   Without this, `typ -> typ MINUS_RANGLE typ` is ambiguous and menhir resolves
   it arbitrarily; only the `typ` rule takes its precedence from this token. */
/* `case ... of` has no terminator, so anything following a branch body is
   ambiguous between continuing the branch and continuing the enclosing term.
   As with dangling-else, the innermost/greedy reading wins: a branch body
   extends as far as possible, and `|` attaches to the nearest `case`.
   LOWEST_CASE exists only to give the two reducing rules a precedence below
   the tokens that may continue a branch. */
%nonassoc LOWEST_CASE
%nonassoc BAR UIDENT LIDENT TRUE FALSE INT LPAREN
%right MINUS_RANGLE
%left OR
%left AND

%type <EHMTT.t * Automata.TreeAutomaton.t> hors
%type <EHMTT.t * [ `Transitions of Automata.TTA.pre_trs | `XTypes of string * Lexing.position | `Both of Lexing.position ] * (Ident.tvar * Ident.tvar RefType.t)> hmtt
%type <[ `Transitions of Automata.TTA.pre_trs | `XTypes of string * Lexing.position | `Both of Lexing.position ]> automaton_section
%type <EHMTT.t> rules
%type <Automata.TreeAutomaton.t> tree_automata
%type <Automata.TTA.pre_trs> tta_transitions
%type <(Ident.tvar * Ident.tvar RefType.t) list> typedefs
%start hors hmtt rules tree_automata tta_transitions typedefs

%%

hors:
  BEGING rules ENDG tree_automata EOF
    { $2, $4 }

hmtt:
  BEGING rules ENDG automaton_section BEGINT typedef ENDT EOF
    { $2, $4, $6 }

/* An EHMTT's automaton is given by its transitions, or by regular tree
   expression type definitions whose types name its states.  Both sections in
   one file are read, as [`Both] with the position where the second begins,
   for the reader to refuse with that position. */
automaton_section:
  BEGINA tta_transitions ENDA
    { `Transitions $2 }
| XTYPES
    { `XTypes $1 }
| BEGINA tta_transitions ENDA XTYPES
    { `Both $startpos($4) }
| XTYPES BEGINA tta_transitions ENDA
    { `Both $startpos($2) }

tree_automata:
  BEGINA tta_transitions ENDA
    { Automata.TreeAutomaton.TTA (Automata.TTA.make $2) }
| BEGINR ata_arities ENDR BEGINATA ata_transitions ENDATA
    { Automata.TreeAutomaton.ATA ($2, Automata.ATA.make $5) }

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

/* [true] and [false] are keywords only inside the formulas of an alternating
   tree automaton ([dnf], [cube]); everywhere else -- a variable, a terminal, a
   case pattern, a state, a base type -- they are ordinary identifiers, as in
   the inputs written for the original EHMTT verifier ([case c of true => ...],
   a state [qBool true -> .]).  Every identifier position reads [lident], never
   the token, so the keywords cannot shadow a name there. */
lident:
  LIDENT
    { $1 }
| TRUE
    { "true" }
| FALSE
    { "false" }

simple_term:
  LPAREN term RPAREN
    { $2 }
| lident
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
| CASE lident OF pats
    { EHMTT.Case(Ident.Tvar $2, $4) }
| COERCE state simple_term
    { 
      let idx = !coerce_idx in
      coerce_idx := idx + 1;
      EHMTT.Coerce(Ident.Tvar $2, $3, idx) 
    }
| COPY simple_term
    { EHMTT.Copy($2) }
| GEN state
    { EHMTT.Tree(Ident.Tvar $2) }

/* A state where a coercion, a generated tree or a specification names one:
   a lower-case name is a state of a [%BEGINA] section, an upper-case one a
   type of a [%BEGINX] section (the reader checks which kind the file has). */
state:
  lident
    { $1 }
| UIDENT
    { $1 }

pats:
  pat %prec LOWEST_CASE
    { [$1] }
| pat BAR pats
    { $1::$3 }

pat:
  lident lidents EQUAL_RANGLE term %prec LOWEST_CASE
    { Ident.Tvar $1, ($2, $4) }

lidents:
  /* empty */
    { [] }
| lident lidents
    { (Ident.Tvar $1) :: $2 }

tta_transitions:
  /* empty */
    { [] }
| lident lident MINUS_RANGLE lidents PERIOD tta_transitions
    { ($1, ($2, List.map Ident.name_of_tvar $4)) :: $6 }
| EOF
    { [] }

ata_arities:
  /* empty */
    { [] }
| lident MINUS_RANGLE INT PERIOD ata_arities
    { ($1, $3) :: $5 }
| EOF
    { [] }

ata_transitions:
  /* empty */
    { [] }
| lident lident MINUS_RANGLE dnf PERIOD ata_transitions
    { ($1, ($2, $4)) :: $6 }
| EOF
    { [] }

dnf:
  FALSE { [] }
| cube { [$1] }
| cube OR dnf { $1 :: $3 }

cube:
  TRUE { [] }
| LPAREN INT COMMA lident RPAREN { [($2, $4)] }
| LPAREN INT COMMA lident RPAREN AND cube { ($2, $4) :: $7 }


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
| lident COLON typ PERIOD
    { Ident.Tvar $1, $3 }

typ:
  state
    { RefType.Base(Ident.Tvar $1) }
| typ MINUS_RANGLE typ
    { RefType.Func($1, $3) }
| LPAREN typ RPAREN
    { $2 }
