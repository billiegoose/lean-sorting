import Init.Data.Random
import LeanSorting.InsertionSort
import LeanSorting.RecursiveMergeSort

namespace LeanSorting.Benchmark

def usage : String :=
  "usage: lean-sorting benchmark [MAX]"

def thresholdNanos : Nat :=
  400 * 1000 * 1000

def parseNatArg (name : String) (value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid {name}: {value}\n{usage}"

partial def randomNumbers (count maxValue : Nat) : IO (List Nat) := do
  let rec build : Nat → List Nat → IO (List Nat)
    | 0, acc => pure acc
    | n + 1, acc => do
        let value ← IO.rand 0 maxValue
        build n (value :: acc)
  build count []

def fingerprint (xs : List Nat) : Nat × Option Nat × Option Nat :=
  (xs.length, xs.head?, xs.getLast?)

def runOnce (sort : List Nat → List Nat) (input : List Nat) : IO Unit := do
  let sorted := sort input
  let fp := fingerprint sorted
  Runtime.hold fp

def runTimed (sort : List Nat → List Nat) (input : List Nat) : IO Nat := do
  -- these two are warmups
  runOnce sort input
  runOnce sort input
  -- the third run is what's measured
  let start ← IO.monoNanosNow
  runOnce sort input
  let stop ← IO.monoNanosNow
  pure (stop - start)

def padLeft (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - s.length) '0') ++ s

def nanosToMillis (nanos : Nat) : String :=
  let whole := nanos / 1000000
  let frac := nanos % 1000000
  s!"{whole}.{padLeft 6 (toString frac)}"

def csvCell : Option Nat → String
  | some nanos => nanosToMillis nanos
  | none => ""

def benchmarkOneSize
    (maxValue size : Nat) (runInsertion runMerge : Bool) :
    IO (Bool × Bool) := do
  let input ← randomNumbers size maxValue
  let insertionNanos? ←
    if runInsertion then
      some <$> runTimed (insertionSort natLeOrder) input
    else
      pure none
  let mergeNanos? ←
    if runMerge then
      some <$> runTimed (mergeSort natLeOrder) input
    else
      pure none
  IO.println s!"{size},{csvCell insertionNanos?},{csvCell mergeNanos?}"
  pure
    (runInsertion && insertionNanos?.any (· <= thresholdNanos),
     runMerge && mergeNanos?.any (· <= thresholdNanos))

partial def benchmarkLoop
    (maxValue size : Nat) (runInsertion runMerge : Bool) : IO Unit := do
  if runInsertion || runMerge then
    let (runInsertion, runMerge) ←
      benchmarkOneSize maxValue size runInsertion runMerge
    benchmarkLoop maxValue (size * 2) runInsertion runMerge

def run (args : List String) : IO Unit := do
  let maxValue ←
    match args with
    | [] => pure 1000000
    | [maxArg] => parseNatArg "max" maxArg
    | _ => throw <| IO.userError usage

  IO.println "N,Insertion Sort,Merge Sort"
  benchmarkLoop maxValue 1 true true

end LeanSorting.Benchmark
