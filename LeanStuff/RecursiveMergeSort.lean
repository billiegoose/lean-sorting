import LeanStuff.Sorting

/-!
# Merge Sort (Recursive, halving)

This is the implementation workspace. In this case, we will start
by defining a function that takes two sorted lists and merges them
into a single sorted list.
-/

def mergeTwoLists {α : Type } (order : TotalOrder α) (xs : List α) (ys : List α) : List α :=
  match xs with
  | [] => ys
  | a :: xrest =>
      match ys with
      | [] => xs
      | b :: yrest =>
          if order.rel a b then
            a :: mergeTwoLists order xrest (b :: yrest)
          else
            b :: mergeTwoLists order (a :: xrest) yrest

example : mergeTwoLists natLeOrder [1, 3, 5] [2, 4, 6] = [1,2,3,4,5,6] := by native_decide

theorem merge_preserves_elements {α : Type}
  (order: TotalOrder α)
  (xs ys: List α) :
  List.Perm (xs ++ ys) (mergeTwoLists order xs ys) := by
  induction xs generalizing ys with
  | nil => simp [mergeTwoLists]
  | cons a xrest xh =>
      induction ys generalizing a xrest with
      | nil => simp [mergeTwoLists]
      | cons b yrest yh =>
          unfold mergeTwoLists
          by_cases h : order.rel a b
          case pos => simpa [if_pos h] using xh (b :: yrest)
          case neg =>
            simp [if_neg h]
            have hy := yh a xrest xh
            exact (List.perm_middle (l₁ := a :: xrest) (l₂ := yrest)).trans
                  (List.Perm.cons b hy)

theorem merge_preserves_ordering {α : Type}
    (order : TotalOrder α)
    (xs : List α) (ys: List α)
    (hx: IsOrdered order xs) (hy: IsOrdered order ys) :
      IsOrdered order (mergeTwoLists order xs ys) := by
  induction xs generalizing ys with
  | nil =>
      simpa [mergeTwoLists] using hy
  | cons a xrest xh =>
      induction ys generalizing a xrest with
      | nil =>
          simpa [mergeTwoLists] using hx
      | cons b yrest yh =>
          unfold mergeTwoLists
          by_cases h : order.rel a b
          · simp [if_pos h]
            unfold IsOrdered at hx hy ⊢
            cases hx with
            | cons hax hxrest =>
                cases hy with
                | cons hby hyrest =>
                    refine List.Pairwise.cons ?_ ?_
                    · intro c hc
                      have hc' : c ∈ xrest ++ b :: yrest :=
                        (merge_preserves_elements order xrest (b :: yrest)).mem_iff.mpr hc
                      cases List.mem_append.mp hc' with
                      | inl hcx =>
                          exact hax c hcx
                      | inr hcby =>
                          simp only [List.mem_cons] at hcby
                          cases hcby with
                          | inl hcb =>
                              cases hcb
                              exact h
                          | inr hcyrest =>
                              exact order.laws.transitive h (hby c hcyrest)
                    · exact xh (b :: yrest) hxrest (List.Pairwise.cons hby hyrest)
          · simp [if_neg h]
            unfold IsOrdered at hx hy ⊢
            cases hx with
            | cons hax hxrest =>
                cases hy with
                | cons hby hyrest =>
                    have hba : order.rel b a :=
                      (order.laws.total a b).resolve_left h
                    refine List.Pairwise.cons ?_ ?_
                    · intro c hc
                      have hc' : c ∈ a :: xrest ++ yrest :=
                        (merge_preserves_elements order (a :: xrest) yrest).mem_iff.mpr hc
                      cases List.mem_append.mp hc' with
                      | inl hcax =>
                          simp only [List.mem_cons] at hcax
                          cases hcax with
                          | inl hca =>
                              cases hca
                              exact hba
                          | inr hcx =>
                              exact order.laws.transitive hba (hax c hcx)
                      | inr hcy =>
                          exact hby c hcy
                    · exact yh a xrest xh (List.Pairwise.cons hax hxrest) hyrest

theorem rel_all_merge {α : Type}
    (order : TotalOrder α)
    (a : α) (xs ys : List α) :
    (∀ b, b ∈ xs → order.rel a b) →
    (∀ b, b ∈ ys → order.rel a b) →
    ∀ b, b ∈ mergeTwoLists order xs ys → order.rel a b := by
  intro hxs hys b hb
  have hb' : b ∈ xs ++ ys :=
    (merge_preserves_elements order xs ys).mem_iff.mpr hb
  grind only [List.mem_append]

theorem merge_preserves_ordering_short {α : Type}
    (order : TotalOrder α)
    (xs ys : List α)
    (hx : IsOrdered order xs) (hy : IsOrdered order ys) :
      IsOrdered order (mergeTwoLists order xs ys) := by
  induction xs generalizing ys with
  | nil => simpa [mergeTwoLists] using hy
  | cons a xrest xh =>
      induction ys generalizing a xrest with
      | nil => simpa [mergeTwoLists] using hx
      | cons b yrest yh =>
          rw [mergeTwoLists]
          unfold IsOrdered at hx hy ⊢
          split
          case isTrue =>
            simp only [List.pairwise_cons] at hx hy ⊢
            refine ⟨rel_all_merge order a xrest (b :: yrest) hx.1 ?_, ?_⟩
            · grind only [List.mem_cons, order.laws.transitive]
            · exact xh (b :: yrest) hx.2 (List.Pairwise.cons hy.1 hy.2)
          case isFalse h =>
            simp only [List.pairwise_cons] at hx hy ⊢
            have hba : order.rel b a := (order.laws.total a b).resolve_left h
            refine ⟨rel_all_merge order b (a :: xrest) yrest ?_ hy.1, ?_⟩
            · grind only [List.mem_cons, order.laws.transitive]
            · exact yh a xrest xh (List.Pairwise.cons hx.1 hx.2) hy.2

-- OK. Now we just need to recursively split the list, prove that terminates, and
-- merge all the lists together.

def mergeSort {α:Type} (order: TotalOrder α) : List α -> List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    let as := a :: b :: rest
    if IsOrdered order as then
      as
    else
      let splitIndex := as.length / 2
      mergeTwoLists order
        (mergeSort order (as.take splitIndex))
        (mergeSort order (as.drop splitIndex))
termination_by as => as.length

example : mergeSort natLeOrder [3,1,4,5,2] = [1,2,3,4,5] := by decide +native

-- theorem merge_sort_returns_ordered_list {α : Type}
--     (order: TotalOrder α) :
--     Sorts order (mergeSort order) := by
