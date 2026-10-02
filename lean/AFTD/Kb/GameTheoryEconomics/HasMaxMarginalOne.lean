import AFTD.Prelude

/-!
# has_max_marginal_one

Topic: fair_division   Node: 356db3fd4731

The subsidy normalisation: every marginal value v(S + e) - v(S) is at most 1, and some marginal value equals 1.
-/

/-- The subsidy normalisation: the largest marginal value of any item is exactly 1. -/
def has_max_marginal_one {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  (∀ S e, v (insert e S) - v S ≤ 1) ∧ ∃ S e, v (insert e S) - v S = 1
