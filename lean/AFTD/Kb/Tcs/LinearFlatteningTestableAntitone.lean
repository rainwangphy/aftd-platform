import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.LinearFlatteningPotencyGtAntitone
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable_antitone

Topic: algebraic_complexity   Node: 8d1b80ae8ac2

Provenance: helper lemma. arXiv:2610.08504 Sec. 1

If the secant variety σ_r((ℂⁿ)⊗³) is testable by the linear flattening method, then so is σ_{r'}((ℂⁿ)⊗³) for every r' ≤ r.
-/

/-- If order r is testable by linear flattenings on (ℂⁿ)⊗³, then every order r' ≤ r is testable. -/
theorem linear_flattening_testable_antitone {n : ℕ} {r r' : ℕ} (hr : r' ≤ r)
    (h : linear_flattening_testable n r) : linear_flattening_testable n r' := by
  obtain ⟨u, v, L, hL⟩ := h
  exact ⟨u, v, L, linear_flattening_potency_gt_antitone L hr hL⟩
