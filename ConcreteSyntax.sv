grammar logic;

lexer class Keyword;

terminal Circuit_t  'circuit'  lexer classes {Keyword};
terminal Series_t   'series'   lexer classes {Keyword};
terminal Parallel_t 'parallel' lexer classes {Keyword};
terminal True_t     'true'     lexer classes {Keyword};
terminal False_t    'false'    lexer classes {Keyword};

terminal Identifier_t /[A-Za-z_\$][A-Za-z_0-9\$]*/ submits to {Keyword};

terminal Semi_t   ';';
terminal Comma_t  ',';
terminal LParen_t '(';
terminal RParen_t ')';
terminal LCurly_t '{';
terminal RCurly_t '}';

terminal AndOp_t '&&' precedence = 1, association = left;
terminal OrOp_t  '||' precedence = 2, association = left;
terminal Not_t   '!'  precedence = 3;

ignore terminal LineComment /[\/][\/].*/;
ignore terminal BlockComment /[\/][\*]([^\*]|[\r\n]|([\*]+([^\*\/]|[\r\n])))*[\*]+[\/]/;
ignore terminal WhiteSpace /[\r\n\t\ ]+/;

synthesized attribute ast<a>::a;

closed nonterminal MultiCircuit_c with ast<MultiCircuit>;

concrete productions top::MultiCircuit_c
| 'circuit' '(' term1::Identifier_t ',' term2::Identifier_t ')' '{' cs::Circuits_c '}' rest::MultiCircuit_c 
  { top.ast = consMultiCircuit(term1.lexeme, term2.lexeme, series(cs.ast), rest.ast); }
| 
  { top.ast = nilMultiCircuit(); }

closed nonterminal Circuits_c with ast<Circuits>;

concrete productions top::Circuits_c
| h::Circuit_c t::Circuits_c
  { top.ast = consCircuit(h.ast, t.ast); }
| h::Circuit_c
  { top.ast = oneCircuit(h.ast); }

closed nonterminal Circuit_c with ast<Circuit>;

concrete productions top::Circuit_c
| e::Expr_c ';'
  { top.ast = switch(e.ast); }
| 'series' '{' cs::Circuits_c '}'
  { top.ast = series(cs.ast); }
| 'parallel' '{' cs::Circuits_c '}'
  { top.ast = parallel(cs.ast); }

closed nonterminal Expr_c with ast<Expr>;

concrete productions top::Expr_c
| 'true'
  { top.ast = trueExpr(); }
| 'false'
  { top.ast = falseExpr(); }
| n::Identifier_t
  { top.ast = varExpr(n.lexeme); }
| e1::Expr_c '&&' e2::Expr_c
  { top.ast = andExpr(e1.ast, e2.ast); }
| e1::Expr_c '||' e2::Expr_c
  { top.ast = orExpr(e1.ast, e2.ast); }
| '!' e1::Expr_c
  { top.ast = notExpr(e1.ast); }
| '(' e1::Expr_c ')'
  { top.ast = e1.ast; }