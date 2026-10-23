import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestableSuccDim
import AFTD.Kb.Tcs.LinearFlatteningTestable

/-!
# linear_flattening_testable_mono_dim

Topic: algebraic_complexity   Node: cb172482d6fa

Provenance: helper lemma. step towards linear_flattening_testable_even_step

Testability is monotone in the tensor dimension: if σ_r((ℂⁿ)⊗³) is testable by linear flattenings and n ≤ m, then so is σ_r((ℂᵐ)⊗³).
-/

/-- General dimension monotonicity for linear-flattening testability at a fixed order, obtained by iterating the one-step padding lemma. -/
theorem linear_flattening_testable_mono_dim {n m r : ℕ} (hnm : n ≤ m)
    (h : linear_flattening_testable n r) : linear_flattening_testable m r := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ k hk ih => exact linear_flattening_testable_succ_dim ih
