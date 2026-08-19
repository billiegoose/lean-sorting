namespace LeanSorting.Cli

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

def parseNatStdinArray : IO (Array Nat) := do
  let nums ← parseNatStdin
  pure nums.toArray

def printNatList (xs : List Nat) : IO Unit :=
  IO.println <| String.intercalate " " (xs.map toString)

def printNatArray (xs : Array Nat) : IO Unit :=
  printNatList xs.toList

def runNatSorter (sort : List Nat → List Nat) : IO Unit := do
  let nums ← parseNatStdin
  printNatList (sort nums)

def runNatArraySorter (sort : Array Nat → Array Nat) : IO Unit := do
  let nums ← parseNatStdinArray
  printNatArray (sort nums)

end LeanSorting.Cli
