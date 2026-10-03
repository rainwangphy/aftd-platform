import AFTD.Prelude

/-!
# leximin_profile

Topic: fair_division   Node: 13a454c32a97

The leximin profile of a utility vector: its entries sorted in increasing order.
-/

/-- The leximin profile of a utility vector: its entries sorted in increasing order. -/
noncomputable def leximin_profile {n : ℕ} (x : Fin n → ℝ) : List ℝ :=
  (List.ofFn x).insertionSort (· ≤ ·)
