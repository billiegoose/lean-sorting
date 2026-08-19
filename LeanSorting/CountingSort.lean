import LeanSorting.Sorting

/-!
# Counting Sort

This algorithm only works on integers. But that's OK because we've been using integers
for all our examples so far.
-/

def countingSort (xs: List Nat) : List Nat :=
  let maxValue := xs.foldl Nat.max 0
  let counts : Array Nat := Id.run do
    let mut counts := Array.replicate (maxValue + 1) 0
    for x in xs do
      counts := counts.modify x (· + 1)
    pure counts
  (expandCounts counts 0 (maxValue + 1) (Array.emptyWithCapacity xs.length)).toList

where
  pushRepeated (out : Array Nat) (value count : Nat) : Array Nat :=
    match count with
    | 0 => out
    | count + 1 => pushRepeated (out.push value) value count

  expandCounts (counts : Array Nat) (value fuel : Nat) (out : Array Nat) : Array Nat :=
    match fuel with
    | 0 => out
    | fuel + 1 =>
        expandCounts counts (value + 1) fuel
          (pushRepeated out value (counts.getD value 0))

example : countingSort [3,1,4,5,2] = [1,2,3,4,5] := by native_decide
example : countingSort [3,1,4,1,2,3] = [1,1,2,3,3,4] := by native_decide
example : countingSort [] = [] := by native_decide

-- theorem counting_sort_sorts_correctly
--     IsNatLeSorter countingSort := by
--   sorry
