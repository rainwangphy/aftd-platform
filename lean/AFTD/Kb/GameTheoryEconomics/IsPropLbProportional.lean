import AFTD.Prelude

/-!
# is_prop_lb_proportional

Topic: fair_division   Node: c47a01e69ef3

Provenance: formalization of a published result. Source: arXiv:2610.19733 Section 4, Proposition 1

An allocation is proportional with respect to the identical valuation profile where each agent's value is `n * λ(S ∩ [0, 1/n])` if each agent receives value at least `1 / n`.
-/

/-- Proportionality under the lower-bound valuation profile `v_i(S) = n * λ(S ∩ [0, 1/n])`. -/
def is_prop_lb_proportional (n : ℕ) (C : Fin n → Set ℝ) : Prop :=
  ∀ i : Fin n, (1 : ENNReal) / (n : ENNReal) ≤ (n : ENNReal) * MeasureTheory.volume (C i ∩ Set.Icc 0 (1 / (n : ℝ)))
