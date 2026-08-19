import LeanSorting.Benchmark
import LeanSorting.Cli
import LeanSorting.GenerateNumbers
import LeanSorting.InsertionSort
import LeanSorting.RecursiveMergeSort

namespace LeanSorting.App

def usage : String :=
  String.intercalate "\n"
    [ "usage: lean-sorting COMMAND [ARGS]"
    , ""
    , "commands:"
    , "  insertion-sort          sort whitespace-separated natural numbers from stdin"
    , "  merge-sort              sort whitespace-separated natural numbers from stdin"
    , "  generate-numbers COUNT [MAX]"
    , "  benchmark [MAX]"
    ]

def run (args : List String) : IO Unit := do
  match args with
  | ["insertion-sort"] =>
      LeanSorting.Cli.runNatSorter (insertionSort natLeOrder)
  | ["merge-sort"] =>
      LeanSorting.Cli.runNatSorter (mergeSort natLeOrder)
  | "generate-numbers" :: args =>
      LeanSorting.GenerateNumbers.run args
  | "benchmark" :: args =>
      LeanSorting.Benchmark.run args
  | [] =>
      throw <| IO.userError usage
  | cmd :: _ =>
      throw <| IO.userError s!"unknown command: {cmd}\n{usage}"

end LeanSorting.App

def main (args : List String) : IO Unit :=
  LeanSorting.App.run args
