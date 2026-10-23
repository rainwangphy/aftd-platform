import AFTD.Prelude

/-!
# is_cake_allocation

Topic: fair_division   Node: 1f1677936dcd

Provenance: formalization of a published result. Source: arXiv:2610.19733 Section 2

An allocation of the cake `[0, 1]` among `n` agents is a measurable partition of `[0, 1]` into `n` bundles `C i`.
-/

/-- A cake allocation of `[0, 1]` for `n` agents is a measurable partition of `[0, 1]`. -/
def is_cake_allocation (n : ℕ) (C : Fin n → Set ℝ) : Prop :=
  (∀ i : Fin n, MeasurableSet (C i)) ∧
  (∀ i j : Fin n, i ≠ j → Disjoint (C i) (C j)) ∧
  (⋃ i : Fin n, C i) = Set.Icc 0 1
