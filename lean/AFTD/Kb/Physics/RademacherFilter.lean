import AFTD.Prelude

/-!
# rademacher_filter

Topic: statistical_mechanics   Node: 1693ca416d00

Provenance: original. Related work: knowledgebase: OP-1152

For a natural number m and a sign configuration s : Fin m → Bool, rademacher_filter m s is the real-valued sequence on ℤ equal to (1 : ℝ) if s ⟨j.toNat, _⟩ is true and (-1 : ℝ) if false for 0 ≤ j < m, and (0 : ℝ) otherwise.
-/

/-- The real sequence on ℤ defined by Rademacher signs on 0 ≤ j < m and 0 elsewhere. -/
def rademacher_filter (m : ℕ) (s : Fin m → Bool) : ℤ → ℝ := fun j =>
  if hj : 0 ≤ j ∧ j < m then
    if s ⟨j.toNat, by omega⟩ then 1 else -1
  else 0
