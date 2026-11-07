/* The union grammar of the HES dialects of ReTHFL, hflmc2 (PaHFL) and MuHFL
   (and MoCHi's and ml2hfl's output, which is ReTHFL's).  The productions and
   precedences are the tools' own (ReTHFL's lib/syntax/parser.mly plus MuHFL's
   [not], [=>], [<=>] and [exists]); where the tools differ only in the
   associativity of [&&] and [||] the tree is built right-associated, which
   means the same.  [%ENV] and [%LTS] are cut off by the lexer.

   Negation is not a constructor of the result: [not], [=>] and [<=>] are
   desugared as MuHFL does and the negation is pushed to the atoms
   ([HflNeg.neg]), refusing a negated predicate-variable application.  A
   quantifier extends as far to the right as possible (its production has the
   lowest precedence). */
%{
open HflSyntax
%}

%token <int> INT
%token <string> LIDENT UIDENT
%token START_HES EOF
%token LPAREN RPAREN
%token TRUE FALSE
%token LAMBDA DOT
%token DEF_G DEF_L
%token FORALL EXISTS
%token PLUS MINUS STAR SLASH PERCENT
%token EQ NEQ LE GE LT GT
%token AND OR NOT IMPLY IFF

%nonassoc QUANT
%left IFF
%right IMPLY
%right OR
%right AND
%nonassoc NOT
%left PLUS MINUS
%left STAR SLASH PERCENT
%nonassoc NEG

%start <HflSyntax.eqn list> main
%%

main:
| START_HES rules=rule+ EOF { rules }

rule:
| name=UIDENT params=lvar* fix=def_fixpoint body=hflz DOT
    { { name; params = List.map (fun x -> (x, None)) params; fix; body } }

def_fixpoint:
| DEF_G { Nu }
| DEF_L { Mu }

hflz:
| lams=lambda* body=and_or_expr
    { List.fold_right (fun x b -> Abs (x, None, b)) (List.concat lams) body }

lambda:
| LAMBDA xs=lvar+ DOT
    { if List.length xs > 1 then HflParseState.saw "multi-variable lambda"; xs }

and_or_expr:
| a=and_or_expr AND b=and_or_expr { And (a, b) }
| a=and_or_expr OR b=and_or_expr { Or (a, b) }
| a=and_or_expr IMPLY b=and_or_expr { Or (HflNeg.neg a, b) }
| a=and_or_expr IFF b=and_or_expr
    { And (Or (HflNeg.neg a, b), Or (HflNeg.neg b, a)) }
| NOT a=and_or_expr { HflNeg.neg a }
| FORALL x=lvar DOT a=and_or_expr %prec QUANT { Forall (x, a) }
| EXISTS x=lvar DOT a=and_or_expr %prec QUANT { Exists (x, a) }
| e=pred_expr { e }

pred_expr:
| a=arith_expr { a }
| a=arith_expr p=pred b=arith_expr { Pred (p, a, b) }

arith_expr:
| e=app_expr { e }
| a=arith_expr PLUS b=arith_expr { Op (Add, a, b) }
| a=arith_expr MINUS b=arith_expr { Op (Sub, a, b) }
| a=arith_expr STAR b=arith_expr { Op (Mul, a, b) }
| a=arith_expr SLASH b=arith_expr { Op (Div, a, b) }
| a=arith_expr PERCENT b=arith_expr { Op (Mod, a, b) }
| MINUS a=arith_expr %prec NEG { Neg a }

app_expr:
| h=atom args=atom* { apps h args }

atom:
| n=INT { Int n }
| TRUE { Bool true }
| FALSE { Bool false }
| x=lvar { Var x }
| x=UIDENT { Var x }
| LPAREN e=hflz RPAREN { e }

%inline pred:
| EQ { Eq }
| NEQ { Neq }
| LE { Le }
| GE { Ge }
| LT { Lt }
| GT { Gt }

lvar:
| x=LIDENT { x }
