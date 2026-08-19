import LeanSorting.Sorting

/-!
# Insertion Sort

This is the implementation workspace. Start by defining an operation that
inserts one natural number into an already sorted list.
-/

def insertIntoSorted {α : Type } (order: TotalOrder α) (xs : List α) (n : α) : List α :=
  match xs with
  | [] => [n]
  | a :: rest => if order.rel a n
        then a :: insertIntoSorted order rest n
        else n :: a :: rest

example : insertIntoSorted natLeOrder [1, 2, 4, 5] 3  = [1,2,3,4,5] := by native_decide

theorem insert_preserves_elements {α : Type}
  (order: TotalOrder α) (xs : List α) (n : α) :
  List.Perm (n :: xs) (insertIntoSorted order xs n) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    unfold insertIntoSorted
    split
    case isFalse => rfl
    case isTrue =>
      exact List.Perm.trans
        (List.Perm.swap a n rest)
        (List.Perm.cons a ih)

-- Theorem: inserting into an ordered list preserves its ordering.
theorem insert_preserves_order {α : Type}
  (order: TotalOrder α) (xs : List α) (n : α) :
  IsOrdered order xs → IsOrdered order (insertIntoSorted order xs n) := by
  induction xs generalizing n with
  | nil =>
    intro hxs
    unfold insertIntoSorted
    unfold IsOrdered
    simp
  | cons a rest ih =>
    intro hxs
    unfold insertIntoSorted
    split -- by_cases h : order.rel a n
    case isTrue h =>
      cases hxs with
      | cons ha hrest =>
        refine List.Pairwise.cons ?_ ?_
        · intro b hb
          -- The inserted tail contains only `n` and the old elements of `rest`.
          have hb' : b ∈ n :: rest :=
            (insert_preserves_elements order rest n).mem_iff.mpr hb
          simp only [List.mem_cons] at hb'
          cases hb' with
          | inl hbn =>
            cases hbn
            exact h
          | inr hbr => exact ha b hbr
        · exact ih n hrest
    case isFalse h =>
      cases hxs with
      | cons ha hrest =>
        refine List.Pairwise.cons ?_ ?_
        · intro b hb
          simp only [List.mem_cons] at hb
          cases hb with
          | inl hba =>
            cases hba
            exact (order.laws.total n a).resolve_right h
          | inr hbr =>
            exact order.laws.transitive
              ((order.laws.total n a).resolve_right h)
              (ha b hbr)
        · exact List.Pairwise.cons ha hrest

theorem insert_preserves_order_short {α : Type}
    (order : TotalOrder α) (xs : List α) (n : α) :
    IsOrdered order xs → IsOrdered order (insertIntoSorted order xs n) := by
  induction xs generalizing n with
  | nil => simp [IsOrdered, insertIntoSorted]
  | cons a rest ih =>
    intro hxs
    unfold insertIntoSorted
    unfold IsOrdered at hxs ⊢
    split
    · simp only [List.pairwise_cons] at hxs ⊢
      have hp := insert_preserves_elements order rest n
      unfold IsOrdered at ih
      grind [hp.mem_iff]
    · simp only [List.pairwise_cons, List.mem_cons] at hxs ⊢
      grind [order.laws.total, order.laws.transitive]

def insertionSort {α : Type} (order: TotalOrder α) (xs : List α) : List α :=
  xs.foldl (insertIntoSorted order) []

example : insertionSort natLeOrder [5,3,1,4,2] = [1,2,3,4,5] := by native_decide
example : insertionSort natLeOrder [1,2,1,2,1] = [1,1,1,2,2] := by native_decide

theorem insertionSort_preserves_order_from_acc {α : Type}
    (order : TotalOrder α) (xs acc : List α) :
    IsOrdered order acc →
    IsOrdered order (xs.foldl (insertIntoSorted order) acc) := by
  intro hacc
  induction xs generalizing acc with
  | nil =>
    simp
    exact hacc
  | cons x xs ih =>
    simp
    exact ih (insertIntoSorted order acc x) (insert_preserves_order order acc x hacc)

theorem insertionSort_preserves_elements_from_acc {α : Type}
    (order : TotalOrder α) (xs acc : List α) :
    List.Perm (xs.reverse ++ acc) (xs.foldl (insertIntoSorted order) acc) := by
  induction xs generalizing acc with
  | nil =>
    simp
  | cons x xs ih =>
    simp
    exact List.Perm.trans
      ((insert_preserves_elements order acc x).append_left xs.reverse)
      (ih (insertIntoSorted order acc x))

theorem insertion_sort_sorts_correctly {α : Type}
    (order: TotalOrder α) :
    Sorts order (insertionSort order) := by
  intro xs
  unfold IsOrderedRearrangement
  unfold insertionSort
  let hnil : IsOrdered order [] := by
    unfold IsOrdered
    simp
  refine ⟨insertionSort_preserves_order_from_acc order xs [] hnil, ?_⟩
  exact (List.reverse_perm xs).symm.trans
    (by simpa using insertionSort_preserves_elements_from_acc order xs [])

theorem insertion_sort_is_nat_le_sorter :
    IsNatLeSorter (insertionSort natLeOrder) := by
  exact insertion_sort_sorts_correctly natLeOrder
