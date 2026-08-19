import LeanSorting.Sorting

/-!
# Counting Sort

This algorithm only works on integers. But that's OK because we've been using integers
for all our examples so far.
-/

def countValues (counts : Array Nat) : List Nat → Array Nat
  | [] => counts
  | x :: xs => countValues (counts.modify x (· + 1)) xs

def countValuesArray (counts : Array Nat) (xs : Array Nat) : Array Nat :=
  xs.foldl (fun counts x => counts.modify x (· + 1)) counts

def expandedCountsList (counts : Array Nat) (value fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      List.replicate (counts.getD value 0) value ++
        expandedCountsList counts (value + 1) fuel

def countingSort (xs : Array Nat) : Array Nat :=
  let maxValue := xs.foldl Nat.max 0
  let counts : Array Nat := countValuesArray (Array.replicate (maxValue + 1) 0) xs
  expandCounts counts 0 (maxValue + 1) (Array.emptyWithCapacity xs.size)

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

def countingSortList (xs : List Nat) : List Nat :=
  let maxValue := xs.foldl Nat.max 0
  let counts : Array Nat := countValues (Array.replicate (maxValue + 1) 0) xs
  (countingSort.expandCounts counts 0 (maxValue + 1) (Array.emptyWithCapacity xs.length)).toList

example : countingSort #[3,1,4,5,2] = #[1,2,3,4,5] := by native_decide
example : countingSort #[3,1,4,1,2,3] = #[1,1,2,3,3,4] := by native_decide
example : countingSort #[] = #[] := by native_decide

example : countingSortList [3,1,4,5,2] = [1,2,3,4,5] := by native_decide
example : countingSortList [3,1,4,1,2,3] = [1,1,2,3,3,4] := by native_decide
example : countingSortList [] = [] := by native_decide

theorem countValuesArray_toArray (counts : Array Nat) (xs : List Nat) :
    countValuesArray counts xs.toArray = countValues counts xs := by
  induction xs generalizing counts with
  | nil =>
      rfl
  | cons x xs ih =>
      unfold countValuesArray
      rw [List.foldl_toArray]
      simp only [List.foldl_cons]
      change
        List.foldl (fun counts x => counts.modify x (fun x => x + 1))
          (counts.modify x (fun x => x + 1)) xs =
        countValues (counts.modify x (fun x => x + 1)) xs
      simpa [countValuesArray, List.foldl_toArray] using
        ih (counts.modify x (· + 1))

theorem countingSort_toArray_toList (xs : List Nat) :
    (countingSort xs.toArray).toList = countingSortList xs := by
  unfold countingSort countingSortList
  simp [countValuesArray_toArray, List.size_toArray]

-- Note: I let GPT 5.5 write all of these theorems itself.

theorem array_getD_modify_of_lt
    (counts : Array Nat) (x a : Nat) (f : Nat → Nat)
    (ha : a < counts.size) :
    (counts.modify x f).getD a 0 =
      if x = a then f (counts.getD a 0) else counts.getD a 0 := by
  unfold Array.getD
  simp [Array.size_modify, ha]
  have hma : a < (counts.modify x f).size := by
    simpa [Array.size_modify] using ha
  rw [Array.getElem_modify (xs := counts) (j := x) (i := a) (f := f) hma]

theorem countValues_size (counts : Array Nat) (xs : List Nat) :
    (countValues counts xs).size = counts.size := by
  induction xs generalizing counts with
  | nil =>
      simp [countValues]
  | cons x xs ih =>
      simp [countValues, ih, Array.size_modify]

theorem countValues_getD_of_lt
    (counts : Array Nat) (xs : List Nat) (a : Nat)
    (ha : a < counts.size) :
    (countValues counts xs).getD a 0 =
      counts.getD a 0 + xs.count a := by
  induction xs generalizing counts with
  | nil =>
      simp [countValues]
  | cons x xs ih =>
      simp only [countValues]
      have hma : a < (counts.modify x (· + 1)).size := by
        simpa [Array.size_modify] using ha
      rw [ih (counts.modify x (· + 1)) hma]
      rw [array_getD_modify_of_lt counts x a (· + 1) ha]
      by_cases hxa : x = a
      · subst x
        simp [List.count_cons_self, Nat.add_assoc, Nat.add_comm]
      · simp [hxa, List.count_cons_of_ne hxa]

theorem pushRepeated_toList
    (out : Array Nat) (value count : Nat) :
    (countingSort.pushRepeated out value count).toList =
      out.toList ++ List.replicate count value := by
  induction count generalizing out with
  | zero =>
      simp [countingSort.pushRepeated]
  | succ count ih =>
      simp [countingSort.pushRepeated, ih, Array.toList_push, List.append_assoc,
        List.replicate]

theorem expandCounts_toList
    (counts : Array Nat) (value fuel : Nat) (out : Array Nat) :
    (countingSort.expandCounts counts value fuel out).toList =
      out.toList ++ expandedCountsList counts value fuel := by
  induction fuel generalizing value out with
  | zero =>
      simp [countingSort.expandCounts, expandedCountsList]
  | succ fuel ih =>
      simp [countingSort.expandCounts, expandedCountsList, ih,
        pushRepeated_toList, List.append_assoc]

theorem mem_expandedCountsList_bounds
    (counts : Array Nat) (value fuel b : Nat) :
    b ∈ expandedCountsList counts value fuel →
      value ≤ b ∧ b < value + fuel := by
  induction fuel generalizing value with
  | zero =>
      simp [expandedCountsList]
  | succ fuel ih =>
      intro hb
      simp [expandedCountsList, List.mem_append, List.mem_replicate] at hb
      cases hb with
      | inl hbRep =>
          rcases hbRep with ⟨_, hbEq⟩
          omega
      | inr hbRest =>
          have h := ih (value + 1) hbRest
          omega

theorem expandedCountsList_ordered
    (counts : Array Nat) (value fuel : Nat) :
    IsOrdered natLeOrder (expandedCountsList counts value fuel) := by
  induction fuel generalizing value with
  | zero =>
      simp [expandedCountsList, IsOrdered]
  | succ fuel ih =>
      unfold IsOrdered at ih ⊢
      rw [expandedCountsList]
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_replicate]
        exact Or.inr (Nat.le_refl value)
      · exact ih (value + 1)
      · intro a ha b hb
        simp [List.mem_replicate] at ha
        rcases ha with ⟨_, haEq⟩
        cases haEq
        exact Nat.le_trans (Nat.le_succ value)
          (mem_expandedCountsList_bounds counts (value + 1) fuel b hb).1

theorem count_expandedCountsList
    (counts : Array Nat) (value fuel a : Nat) :
    (expandedCountsList counts value fuel).count a =
      if value ≤ a ∧ a < value + fuel then counts.getD a 0 else 0 := by
  induction fuel generalizing value with
  | zero =>
      by_cases h : value ≤ a ∧ a < value
      · omega
      · simp [expandedCountsList, h]
  | succ fuel ih =>
      rw [expandedCountsList]
      rw [List.count_append]
      rw [List.count_replicate]
      rw [ih (value + 1)]
      by_cases hEq : value = a
      · subst a
        have hRange : ¬ (value + 1 ≤ value ∧ value < value + 1 + fuel) := by
          omega
        have hOuter : value ≤ value ∧ value < value + (fuel + 1) := by
          omega
        simp [hRange, hOuter]
      · have hNe : (value == a) = false := by
          exact Bool.eq_false_iff.mpr (mt LawfulBEq.eq_of_beq hEq)
        by_cases hRange : value + 1 ≤ a ∧ a < value + 1 + fuel
        · have hOuter : value ≤ a ∧ a < value + (fuel + 1) := by omega
          simp [hNe, hRange, hOuter]
        · have hOuterIff : (value ≤ a ∧ a < value + (fuel + 1)) ↔
              (value + 1 ≤ a ∧ a < value + 1 + fuel) := by
            constructor <;> intro h <;> omega
          have hOuter : ¬ (value ≤ a ∧ a < value + (fuel + 1)) := by
            intro h
            exact hRange (hOuterIff.mp h)
          simp [hNe, hRange, hOuter]

theorem foldl_max_le_result (xs : List Nat) (seed : Nat) :
    seed ≤ xs.foldl Nat.max seed := by
  induction xs generalizing seed with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left seed x) (ih (Nat.max seed x))

theorem le_foldl_max_of_mem (xs : List Nat) (seed a : Nat) :
    a ∈ xs → a ≤ xs.foldl Nat.max seed := by
  induction xs generalizing seed with
  | nil =>
      simp
  | cons x xs ih =>
      intro ha
      simp only [List.mem_cons] at ha
      simp [List.foldl_cons]
      cases ha with
      | inl h =>
          subst a
          exact Nat.le_trans (Nat.le_max_right seed x)
            (foldl_max_le_result xs (Nat.max seed x))
      | inr h =>
          exact ih (Nat.max seed x) h

theorem count_eq_zero_of_gt_foldl_max
    (xs : List Nat) (a : Nat)
    (hgt : xs.foldl Nat.max 0 < a) :
    xs.count a = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro ha
  have hle := le_foldl_max_of_mem xs 0 a ha
  omega

theorem replicate_zero_getD (n a : Nat) :
    (Array.replicate n 0).getD a 0 = 0 := by
  unfold Array.getD
  split
  · simp
  · simp

theorem countValues_from_zero_getD
    (xs : List Nat) (a : Nat)
    (ha : a < (Array.replicate (xs.foldl Nat.max 0 + 1) 0).size) :
    (countValues (Array.replicate (xs.foldl Nat.max 0 + 1) 0) xs).getD a 0 =
      xs.count a := by
  rw [countValues_getD_of_lt]
  · have hzero :
        (Array.replicate (xs.foldl Nat.max 0 + 1) 0).getD a 0 = 0 :=
        replicate_zero_getD (xs.foldl Nat.max 0 + 1) a
    rw [hzero]
    omega
  · exact ha

theorem countingSort_eq_expandedCountsList (xs : List Nat) :
    countingSortList xs =
      expandedCountsList
        (countValues (Array.replicate (xs.foldl Nat.max 0 + 1) 0) xs)
        0
        (xs.foldl Nat.max 0 + 1) := by
  unfold countingSortList
  rw [expandCounts_toList]
  simp [Array.emptyWithCapacity]

theorem countingSort_preserves_order (xs : List Nat) :
    IsOrdered natLeOrder (countingSortList xs) := by
  rw [countingSort_eq_expandedCountsList]
  exact expandedCountsList_ordered
    (countValues (Array.replicate (xs.foldl Nat.max 0 + 1) 0) xs)
    0
    (xs.foldl Nat.max 0 + 1)

theorem countingSort_preserves_elements (xs : List Nat) :
    List.Perm xs (countingSortList xs) := by
  rw [List.perm_iff_count]
  intro a
  rw [countingSort_eq_expandedCountsList]
  rw [count_expandedCountsList]
  by_cases ha : a < xs.foldl Nat.max 0 + 1
  · have hsize : a < (Array.replicate (xs.foldl Nat.max 0 + 1) 0).size := by
      simpa [Array.size_replicate] using ha
    have hcount := countValues_from_zero_getD xs a hsize
    simp [ha, hcount]
  · have hgt : xs.foldl Nat.max 0 < a := by omega
    have hzero := count_eq_zero_of_gt_foldl_max xs a hgt
    simp [ha, hzero]

theorem counting_sort_sorts_correctly :
    IsNatLeSorter (fun xs => (countingSort xs.toArray).toList) := by
  intro xs
  simp [countingSort_toArray_toList]
  exact ⟨countingSort_preserves_order xs, countingSort_preserves_elements xs⟩
