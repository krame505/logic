grammar logic;

type Edge = Pair<String String>;
type Graph = [Pair<Edge Expr>];

function addConnection
Graph ::= t1::String t2::String e::Expr graph::Graph
{
  return
    case lookupBy(edgeEq, pair(t1, t2), graph) of
      just(e1) -> pair(pair(t1, t2), orExpr(e, e1)) :: removePairBy(edgeEq, pair(t1, t2), graph)
    | nothing() -> pair(pair(t1, t2), e) :: graph
    end;
}

function lookupConnection
Expr ::= t1::String t2::String graph::Graph
{
  return
    case lookupBy(edgeEq, pair(t1, t2), graph) of
      just(e) -> e
    | nothing() -> if t1 == t2 then trueExpr() else falseExpr()
    end;
}

function transitiveClosure
Graph ::= allTerminals::[String] terminals::[String] graph::Graph
{
  return
    case terminals of
      t2 :: rest ->
        transitiveClosure(
          allTerminals, rest, 
          do (bindList, returnList) {
            t1::String <- allTerminals;
            t3::String <- allTerminals;
            e13::Expr = lookupConnection(t1, t3, graph);
            e12::Expr = lookupConnection(t1, t2, graph);
            e23::Expr = lookupConnection(t2, t3, graph);
            return pair(pair(t1, t3), simplify(orExpr(e13, andExpr(e12, e23))));
          })
    | [] -> graph
    end;
}

function edgeEq
Boolean ::= p1::Edge p2::Edge
{
  return p1.fst == p2.fst && p1.snd == p2.snd;
}

function removePairBy
[Pair<a b>] ::= eq::(Boolean ::= a a)  x::a  xs::[Pair<a b>]
{
 return if null(xs) then []
        else (if eq(x,head(xs).fst) then [] else [head(xs)]) ++ removePairBy(eq, x, tail(xs));
}