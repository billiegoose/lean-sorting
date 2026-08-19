namespace LeanStuff.Cli

def parseNatToken (token : String) : IO Nat :=
  match token.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid natural number: {token}"

def parseNatStdin : IO (List Nat) := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  input.split Char.isWhitespace
    |>.toStringList
    |>.filter (fun token => !token.isEmpty)
    |>.mapM parseNatToken

def printNatList (xs : List Nat) : IO Unit :=
  IO.println <| String.intercalate " " (xs.map toString)

def runNatSorter (sort : List Nat → List Nat) : IO Unit := do
  let nums ← parseNatStdin
  printNatList (sort nums)

end LeanStuff.Cli
