import Init.Data.Random

def usage : String :=
  "usage: generate-numbers COUNT [MAX]"

def parseNatArg (name : String) (value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid {name}: {value}\n{usage}"

partial def writeRandomNumbers (count maxValue : Nat) : IO Unit := do
  let stdout ← IO.getStdout
  let rec loop : Nat → IO Unit
    | 0 => pure ()
    | n + 1 => do
        let value ← IO.rand 0 maxValue
        stdout.putStrLn (toString value)
        loop n
  loop count

def main (args : List String) : IO Unit := do
  match args with
  | [countArg] =>
      let count ← parseNatArg "count" countArg
      writeRandomNumbers count 1000000
  | [countArg, maxArg] =>
      let count ← parseNatArg "count" countArg
      let maxValue ← parseNatArg "max" maxArg
      writeRandomNumbers count maxValue
  | _ =>
      throw <| IO.userError usage
