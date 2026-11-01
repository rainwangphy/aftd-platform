import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasShiftEquiv
import AFTD.Kb.Tcs.DualMelasIsNonDegenerate
import AFTD.Kb.Tcs.DualMelasShiftEquivImpEvalMulEvalEq
import AFTD.Kb.Tcs.DualMelasEvalMulEvalEqImpShiftEquiv

/-!
# dual_melas_non_degenerate_orbit_shift_equiv_iff

Topic: information   Node: f609884043e0

Provenance: formalization of a published result. Source: arXiv:2610.38017 Lemma 5

Let k ≥ 3, let F be a finite field of order 2^k, and let α ∈ F be primitive of order 2^k - 1. For binary polynomials f and g such that f is non-degenerate (neither α nor α⁻¹ is a root of f), f and g are shift-equivalent modulo the product of the minimal polynomials of α and α⁻¹ if and only if f(α) * f(α⁻¹) = g(α) * g(α⁻¹).
-/

/-- Characterization of non-degenerate orbits: shift equivalence modulo dual Melas generator iff f(α)f(α⁻¹) = g(α)g(α⁻¹). -/
theorem dual_melas_non_degenerate_orbit_shift_equiv_iff
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (k : ℕ) (hk : 3 ≤ k) (hcard : Fintype.card F = 2 ^ k)
    (α : F) (hprim : IsPrimitiveRoot α (2 ^ k - 1))
    (f g : Polynomial (ZMod 2))
    (hnondeg : dual_melas_is_non_degenerate α f) :
    dual_melas_shift_equiv α f g ↔
      Polynomial.aeval α f * Polynomial.aeval α⁻¹ f =
        Polynomial.aeval α g * Polynomial.aeval α⁻¹ g := by
  constructor
  · intro hsim
    have hn : 2 ^ k - 1 ≠ 0 := by
      have h3 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    exact dual_melas_shift_equiv_imp_eval_mul_eval_eq α (IsPrimitiveRoot.ne_zero hprim hn) f g hsim
  · intro heval
    exact dual_melas_eval_mul_eval_eq_imp_shift_equiv k hk hcard α hprim f g hnondeg heval
