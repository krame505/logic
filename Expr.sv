grammar logic;

synthesized attribute pp::String;
synthesized attribute vars::[String];

inherited attribute isEqualTo::Expr;
synthesized attribute isEqual::Boolean;
autocopy attribute substitutions::[Pair<String Expr>];
synthesized attribute substituted::Expr;

synthesized attribute reduced::Expr;
synthesized attribute dnf::[[Expr]];
synthesized attribute cnf::[[Expr]];

nonterminal Expr with pp, vars, isEqualTo, isEqual, substitutions, substituted, reduced, dnf, cnf;

abstract production trueExpr
top::Expr ::=
{
  propagate substituted, reduced;
  top.pp = "true";
  top.vars = [];
  top.isEqual =
    case top.isEqualTo of
      trueExpr() -> true
    | _ -> false
    end;
  top.dnf = [[]];
  top.cnf = [];
}

abstract production falseExpr
top::Expr ::=
{
  propagate substituted, reduced;
  top.pp = "false";
  top.vars = [];
  top.isEqual =
    case top.isEqualTo of
      falseExpr() -> true
    | _ -> false
    end;
  top.dnf = [];
  top.cnf = [[]];
}

abstract production varExpr
top::Expr ::= n::String
{
  propagate reduced;
  top.pp = n;
  top.vars = [n];
  top.substituted =
    case lookupBy(stringEq, n, top.substitutions) of
      just(e) -> e
    | nothing() -> top
    end;
  top.isEqual =
    case top.isEqualTo of
      varExpr(n1) -> n == n1
    | _ -> false
    end;
  top.dnf = [[varExpr(n)]];
  top.cnf = [[varExpr(n)]];
}

abstract production andExpr
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp =
    case e1 of
      orExpr(_, _) -> s"(${e1.pp})"
    | _ -> e1.pp
    end ++ " && " ++
    case e2 of
      orExpr(_, _) -> s"(${e2.pp})"
    | _ -> e2.pp
    end;
  top.vars = unionBy(stringEq, e1.vars, e2.vars);
  top.isEqual =
    case top.isEqualTo of
      andExpr(_, _) -> e1.isEqual && e2.isEqual
    | _ -> false
    end;
  e1.isEqualTo =
    case top.isEqualTo of
      andExpr(e, _) -> e
    end;
  e2.isEqualTo =
    case top.isEqualTo of
      andExpr(_, e) -> e
    end;
  top.reduced =
    case e1.reduced, e2.reduced of
      falseExpr(), _ -> falseExpr()
    | _, falseExpr() -> falseExpr()
    | trueExpr(), e -> e
    | e, trueExpr() -> e
    | notExpr(e1), notExpr(e2) -> notExpr(orExpr(e1, e2)).reduced
    | e1, e2 -> andExpr(e1, e2)
    end;
  top.dnf =
    do (bindList, returnList) {
      c1::[Expr] <- e1.dnf;
      c2::[Expr] <- e2.dnf;
      return c1 ++ c2;
    };
  top.cnf = e1.cnf ++ e2.cnf;
}

abstract production orExpr
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp =
    case e1 of
      andExpr(_, _) -> s"(${e1.pp})"
    | _ -> e1.pp
    end ++ " || " ++
    case e2 of
      andExpr(_, _) -> s"(${e2.pp})"
    | _ -> e2.pp
    end;
  top.vars = unionBy(stringEq, e1.vars, e2.vars);
  top.isEqual =
    case top.isEqualTo of
      orExpr(_, _) -> e1.isEqual && e2.isEqual
    | _ -> false
    end;
  e1.isEqualTo =
    case top.isEqualTo of
      orExpr(e, _) -> e
    end;
  e2.isEqualTo =
    case top.isEqualTo of
      orExpr(_, e) -> e
    end;
  top.reduced =
    case e1.reduced, e2.reduced of
      falseExpr(), e -> e
    | e, falseExpr() -> e
    | trueExpr(), _ -> trueExpr()
    | _, trueExpr() -> trueExpr()
    | notExpr(e1), notExpr(e2) -> notExpr(andExpr(e1, e2)).reduced
    | e1, e2 -> orExpr(e1, e2)
    end;
  top.dnf = e1.dnf ++ e2.dnf;
  top.cnf =
    do (bindList, returnList) {
      c1::[Expr] <- e1.cnf;
      c2::[Expr] <- e2.cnf;
      return c1 ++ c2;
    };
}

abstract production notExpr
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp =
    case e of
      andExpr(_, _) -> s"!(${e.pp})"
    | orExpr(_, _) -> s"!(${e.pp})"
    | _ -> s"!${e.pp}"
    end;
  top.vars = e.vars;
  top.isEqual =
    case top.isEqualTo of
      notExpr(_) -> e.isEqual
    | _ -> false
    end;
  e.isEqualTo =
    case top.isEqualTo of
      notExpr(e1) -> e1
    end;
  top.reduced =
    case e.reduced of
      falseExpr() -> trueExpr()
    | trueExpr() -> falseExpr()
    | notExpr(andExpr(notExpr(e1), e2)) -> orExpr(e1, notExpr(e2)).reduced
    | notExpr(andExpr(e1, notExpr(e2))) -> orExpr(notExpr(e1), e2).reduced
    | notExpr(orExpr(notExpr(e1), e2)) -> andExpr(e1, notExpr(e2)).reduced
    | notExpr(orExpr(e1, notExpr(e2))) -> andExpr(notExpr(e1), e2).reduced
    | e -> notExpr(e)
    end;
  top.dnf =
    do (bindList, returnList) {
      c::[Expr] <- e.dnf;
      return map(notExpr, c);
    };
  top.cnf =
    do (bindList, returnList) {
      c::[Expr] <- e.cnf;
      return map(notExpr, c);
    };
}

function simplify
Expr ::= e::Expr
{
  local orClauses::[Expr] =
    do (bindList, returnList) {
      c::[Either<String String>] <- toDNFClauses(e);
      return
        foldr(
          andExpr,
          trueExpr(),
          nubBy(exprEqual, map(literalToExpr, sortBy(literalLte, c))));
    };

  return
    foldr(
      orExpr,
      falseExpr(),
      nubBy(
        clauseRedundant,
        reverse(
          nubBy(
            clauseRedundant,
            filter(clauseUseful, orClauses))))).reduced;
}

function substitute
Expr ::= subs::[Pair<String Expr>] e::Expr
{
  e.substitutions = subs;
  return e.substituted;
}

function exprEqual
Boolean ::= e1::Expr e2::Expr
{
  e1.isEqualTo = e2;
  return e1.isEqual;
}

-- Literal in clause represented as left(name) = varExpr(name), right(name) = notExpr(varExpr(name))
function toDNFClauses
[[Either<String String>]] ::= e::Expr
{
  return
    do (bindList, returnList) {
      elem::Pair<[Pair<String Expr>] [Either<String String>]> <-
        zipWith(pair, allAssignments(e.vars), allTerms(e.vars));
      case substitute(elem.fst, e).reduced of
        trueExpr() -> [elem.snd]
      | falseExpr() -> []
      end;
    };
}

function allAssignments
[[Pair<String Expr>]] ::= vars::[String]
{
  return
    case vars of
      h :: t -> 
      do (bindList, returnList) {
        assign::[Pair<String Expr>] <- allAssignments(t);
        [pair(h, trueExpr()) :: assign, pair(h, falseExpr()) :: assign];
      }
    | [] -> [[]]
    end;
}

function allTerms
[[Either<String String>]] ::= vars::[String]
{
  return
    case vars of
      h :: t -> 
      do (bindList, returnList) {
        rest::[Either<String String>] <- allTerms(t);
        [left(h) :: rest, right(h) :: rest];
      }
    | [] -> [[]]
    end;
}

function literalToExpr
Expr ::= l::Either<String String>
{
  return
    case l of
      left(n) -> varExpr(n)
    | right(n) -> notExpr(varExpr(n))
    end;
}

function literalEqual
Boolean ::= l1::Either<String String> l2::Either<String String>
{
  return
    case l1, l2 of
      left(n1), left(n2) -> n1 == n2
    | right(n1), right(n2) -> n1 == n2
    | _, _ -> false
    end;
}

function literalLte
Boolean ::= l1::Either<String String> l2::Either<String String>
{
  return
    case l1, l2 of
      left(n1), left(n2) -> stringLte(n1, n2)
    | right(n1), right(n2) -> stringLte(n1, n2)
    | left(_), right(_) -> true
    | right(_), left(_) -> false
    end;
}

-- True if e1 is implied by e2
function clauseRedundant
Boolean ::= e1::Expr e2::Expr
{
  return clauseRedundantHelp(e1.vars, orExpr(e1, notExpr(e2)));
}

function clauseRedundantHelp
Boolean ::= vars::[String] e::Expr
{
  return
    case vars of
      h :: t ->
        clauseRedundantHelp(t, substitute([pair(h, trueExpr())], e)) &&
        clauseRedundantHelp(t, substitute([pair(h, falseExpr())], e))
    | [] ->
        case e.reduced of
          trueExpr() -> true
        | _ -> false
        end
    end;
}

-- True if e is not always false
function clauseUseful
Boolean ::= e::Expr
{
  return clauseUsefulHelp(e.vars, e);
}

function clauseUsefulHelp
Boolean ::= vars::[String] e::Expr
{
  return
    case vars of
      h :: t ->
        clauseUsefulHelp(t, substitute([pair(h, trueExpr())], e)) ||
        clauseUsefulHelp(t, substitute([pair(h, falseExpr())], e))
    | [] ->
        case e.reduced of
          trueExpr() -> true
        | _ -> false
        end
    end;
}