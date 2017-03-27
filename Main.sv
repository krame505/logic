grammar logic;

parser parse :: MultiCircuit_c {
  logic;
}

function main
IOVal<Integer> ::= args::[String] ioIn::IO
{
  local fileName::String = head(args);
  local options::[String] = tail(args);

  local result::IOMonad<Integer> = do (bindIO, returnIO) {
    if null(args) then {
      printM("Usage: java -jar circuit.jar [filename] (flags)\n");
      return 1;
    } else {
      isF::Boolean <- isFileM(fileName);
      if !isF then {
        printM("File \"" ++ fileName ++ "\" not found.\n");
        return 2;
      } else {
        text :: String <- readFileM(fileName);
        result :: ParseResult<MultiCircuit_c> = parse(text, fileName);
        if !result.parseSuccess then {
          printM(result.parseErrors ++ "\n");
          return 3;
        } else {
          ast :: MultiCircuit = result.parseTree.ast;
          allPaths :: [Pair<Pair<String String> Expr>] = paths(ast);
          allPathPPs :: [String] = do (bindList, returnList) {
            t1::String <- ast.terminals;
            t2::String <- ast.terminals;
            path::Expr = lookupConnection(t1, t2, allPaths);
            if compareString(t1, t2) < 0 then
              return s"${t1} -> ${t2}: ${path.pp}";
            else [];
          };
          printM(implode("\n", allPathPPs) ++ "\n");
          writeFileM("out.dot", dotPP(ast));
          return 0;
        }
      }
    }
  };
  
  return evalIO(result, ioIn);
}