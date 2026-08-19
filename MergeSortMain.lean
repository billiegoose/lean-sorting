import LeanStuff.Cli
import LeanStuff.RecursiveMergeSort

def main : IO Unit :=
  LeanStuff.Cli.runNatSorter (mergeSort natLeOrder)
