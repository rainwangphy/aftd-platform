import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable

/-!
# linear_flattening_even_potency_induction

Topic: algebraic_complexity   Node: 55bfd0ca1fa0

Provenance: helper lemma. step towards op100_linear_flattening_potency_gt_even

If the secant variety σ_6((ℂ⁴)⊗³) is testable by linear flattenings, and if for all even k ≥ 4 testability of σ_{2k-2}((ℂᵏ)⊗³) implies testability of σ_{2(k+2)-2}((ℂ^{k+2})⊗³), then σ_{2n-2}((ℂⁿ)⊗³) is testable for all even n ≥ 4.
-/

/-- Induction principle for even numbers n ≥ 4 tailored to linear flattening testability: testability at 4 6 and the step from k to k+2 imply testability for all even n ≥ 4. -/
theorem linear_flattening_even_potency_induction
    (h4 : linear_flattening_testable 4 6)
    (hstep : ∀ k, 4 ≤ k → Even k → linear_flattening_testable k (2 * k - 2) → linear_flattening_testable (k + 2) (2 * (k + 2) - 2)) :
    ∀ n, 4 ≤ n → Even n → linear_flattening_testable n (2 * n - 2) := by
  have H : ∀ d : ℕ, linear_flattening_testable (4 + 2 * d) (2 * (4 + 2 * d) - 2) := by
    intro d
    induction d with
    | zero =>
      exact h4
    | succ d ih =>
      have hstep_app := hstep (4 + 2 * d) (by omega) ⟨2 + d, by omega⟩ ih
      exact hstep_app
  intro n hn heven
  obtain ⟨r, hr⟩ := heven
  have : n = 4 + 2 * (r - 2) := by omega
  rw [this]
  exact H (r - 2)
