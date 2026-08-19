import LeanStuff.Cli
import LeanStuff.InsertionSort

def main : IO Unit :=
  LeanStuff.Cli.runNatSorter (insertionSort natLeOrder)
