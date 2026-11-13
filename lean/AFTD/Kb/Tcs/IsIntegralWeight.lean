import AFTD.Prelude

/-!
# IsIntegralWeight

Topic: graphs   Node: 5a2bd11a84ae

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

A weighting vector is integral if every component is a natural number.
-/

/-- Integrality of a nonnegative weight vector. -/
def IsIntegralWeight {α : Type*} (w : α → ℝ) : Prop :=
  ∀ a, ∃ n : ℕ, w a = n
