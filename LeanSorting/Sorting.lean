import Init.Data.List.Perm

open scoped List

/-!
# What does it mean to sort?

Before we implement a sorting algorithm, we write down its *contract*.
For a list `output` to be a correct sorted version of `input`, it must:

1. be ordered according to a decidable total order; and
2. contain exactly the same elements as `input`, including duplicates.

`List.Perm` expresses the second condition. It means that one list can be
obtained from the other by reordering its elements.

An order is a relation `r : α → α → Prop`. We call it a total order when
any two elements are comparable (https://en.wikipedia.org/wiki/Total_order).
That means our relation (sometimes called a comparison function) must have
the following properties.

1. reflexive: `r a a` is always True;
2. antisymmetric: if `r a b` and `r b a`, then `a = b`;
3. transitive: if `r a b` and `r b c`, then `r a c`; and
4. total: for any `a` and `b`, `r a b` or `r b a`.

For an ordered list, we use `xs.Pairwise r`: every earlier item in `xs` is
related by `r` to every later item. We also require each comparison to be
decidable, allowing Lean to compute whether a concrete list is sorted.
-/

structure IsTotalOrder {α : Type} (r : α → α → Prop) : Prop where
  reflexive : ∀ a, r a a
  antisymmetric : ∀ {a b}, r a b → r b a → a = b
  transitive : ∀ {a b c}, r a b → r b c → r a c
  total : ∀ a b, r a b ∨ r b a

structure TotalOrder (α : Type) where
  rel : α → α → Prop
  laws : IsTotalOrder rel
  decidableRel : DecidableRel rel

instance (order : TotalOrder α) : DecidableRel order.rel :=
  order.decidableRel

-- Theorem: (· ≤ ·) provides a total ordering over the Natural numbers
-- Note:  (· ≥ ·) would also work
theorem natLeIsTotalOrder : IsTotalOrder (fun a b : Nat => a ≤ b) := by
  exact {
    reflexive := Nat.le_refl
    antisymmetric := Nat.le_antisymm
    transitive := Nat.le_trans
    total := Nat.le_total
  }

def natLeOrder : TotalOrder Nat := {
  rel := (· ≤ ·)
  laws := natLeIsTotalOrder
  decidableRel := fun _ _ => inferInstance
}

def IsOrdered {α : Type} (order : TotalOrder α) (xs : List α) : Prop :=
  xs.Pairwise order.rel

def NatIncreasingOrder (xs: List Nat) := IsOrdered natLeOrder xs

instance {α : Type} (order : TotalOrder α) (xs : List α) :
    Decidable (IsOrdered order xs) := by
  unfold IsOrdered
  infer_instance

example : IsOrdered natLeOrder [1, 2, 2, 5] := by decide

example : ¬ IsOrdered natLeOrder [5, 3, 1] := by decide

-- Our first attempts to define sorting did not require a total ordering.
-- This is here to make sure that ≠ is a counter-example
example : ¬ IsTotalOrder (fun a b : Nat => a ≠ b) := by
  intro h
  exact (h.reflexive 1) rfl


def IsOrderedRearrangement {α : Type} (order : TotalOrder α)
    (input output : List α) : Prop :=
  IsOrdered order output ∧ List.Perm input output

instance {α : Type} (order : TotalOrder α) (input output : List α) :
    Decidable (IsOrderedRearrangement order input output) := by
  letI : DecidableEq α := fun a b =>
    match order.decidableRel a b with
    | isTrue hab =>
      match order.decidableRel b a with
      | isTrue hba => isTrue (order.laws.antisymmetric hab hba)
      | isFalse hba => isFalse (by
        intro habEq
        cases habEq
        exact hba (order.laws.reflexive a))
    | isFalse hab => isFalse (by
      intro habEq
      cases habEq
      exact hab (order.laws.reflexive a))
  unfold IsOrderedRearrangement
  infer_instance

example : IsOrderedRearrangement natLeOrder [3, 1, 3] [1, 3, 3] := by decide

/-!
A sorting algorithm is a function which meets that contract for *every* input.
We have deliberately kept the element type and ordering relation general. For
ordinary number sorting, we will use `Nat` and `(· ≤ ·)`.
-/

def Sorts {α : Type} (order : TotalOrder α) (sort : List α → List α) : Prop :=
  ∀ input, IsOrderedRearrangement order input (sort input)

def IsNatLeSorter (sort : List Nat → List Nat) : Prop :=
  Sorts natLeOrder sort
