grammar logic;

imports core:monad;

synthesized attribute dotLName::String;
synthesized attribute dotRName::String;
synthesized attribute dotPP::String;

synthesized attribute terminals::[String];
synthesized attribute toGraph::Graph;

nonterminal MultiCircuit with dotPP, terminals, toGraph;

abstract production consMultiCircuit
top::MultiCircuit ::= lTerm::String rTerm::String body::Circuit t::MultiCircuit
{
  top.dotPP =
    s"  ${lTerm} -- ${body.dotLName};\n" ++
    body.dotPP ++
    s"  ${body.dotRName} -- ${rTerm};\n" ++
    t.dotPP;

  top.terminals =
    (if !containsBy(stringEq, lTerm, t.terminals)
     then [lTerm]
     else []) ++
    (if !containsBy(stringEq, rTerm, t.terminals)
     then [rTerm]
     else []) ++ t.terminals;
  top.toGraph =
    addConnection(
      lTerm, rTerm, body.toExpr,
      addConnection(
        rTerm, lTerm, body.toExpr,
        t.toGraph));
}

abstract production nilMultiCircuit
top::MultiCircuit ::= 
{
  top.dotPP = "";
  top.terminals = [];
  top.toGraph = [];
}

synthesized attribute toExpr::Expr;

nonterminal Circuit with dotLName, dotRName, dotPP, toExpr;

abstract production switch
top::Circuit ::= expr::Expr
{
  local name::String = "switch_" ++ toString(genInt());
  top.dotLName = name;
  top.dotRName = name;
  top.dotPP = s"  ${name} [label = \"${expr.pp}\", shape=box];\n";
  
  top.toExpr = expr;
}

abstract production series
top::Circuit ::= cs::Circuits
{
  top.dotLName = cs.dotLName;
  top.dotRName = cs.dotRName;
  top.dotPP = cs.seriesDotPP;

  top.toExpr = cs.toAndExpr;
}

abstract production parallel
top::Circuit ::= cs::Circuits
{
  top.dotLName = "parallel_" ++ toString(genInt());
  top.dotRName = "parallel_" ++ toString(genInt());
  top.dotPP =
    s"  ${top.dotLName} [shape=point];\n  ${top.dotRName} [shape=point];" ++
    cs.parallelDotPP;
  cs.parallelDotLNameIn = top.dotLName;
  cs.parallelDotRNameIn = top.dotRName;

  top.toExpr = cs.toOrExpr;
}

autocopy attribute parallelDotLNameIn::String;
autocopy attribute parallelDotRNameIn::String;

synthesized attribute seriesDotPP::String;
synthesized attribute parallelDotPP::String;

synthesized attribute toAndExpr::Expr;
synthesized attribute toOrExpr::Expr;

nonterminal Circuits with dotLName, dotRName, parallelDotLNameIn, parallelDotRNameIn, seriesDotPP, parallelDotPP, toAndExpr, toOrExpr;

abstract production consCircuit
top::Circuits ::= h::Circuit t::Circuits
{
  top.seriesDotPP = h.dotPP ++ t.seriesDotPP ++ s"  ${h.dotRName} -- ${t.dotLName};\n";
  top.parallelDotPP =
    s"  ${top.parallelDotLNameIn} -- ${h.dotLName};\n" ++
    h.dotPP ++
    s"  ${h.dotRName} -- ${top.parallelDotRNameIn};\n" ++
    t.parallelDotPP;
  top.dotLName = h.dotLName;
  top.dotRName = t.dotRName;
  top.toAndExpr = andExpr(h.toExpr, t.toAndExpr);
  top.toOrExpr = orExpr(h.toExpr, t.toOrExpr);
}

abstract production oneCircuit
top::Circuits ::= h::Circuit
{
  top.seriesDotPP = h.dotPP;
  top.parallelDotPP =
    s"  ${top.parallelDotLNameIn} -- ${h.dotLName};\n" ++
    h.dotPP ++
    s"  ${h.dotRName} -- ${top.parallelDotRNameIn};\n";
  top.dotLName = h.dotLName;
  top.dotRName = h.dotRName;
  top.toAndExpr = h.toExpr;
  top.toOrExpr = h.toExpr;
}

function dotPP
String ::= c::MultiCircuit
{
  return s"""
graph {
graph [splines=ortho];
${c.dotPP}
}""";
}

function paths
Graph ::= c::MultiCircuit
{
  return transitiveClosure(c.terminals, c.terminals, c.toGraph);
}