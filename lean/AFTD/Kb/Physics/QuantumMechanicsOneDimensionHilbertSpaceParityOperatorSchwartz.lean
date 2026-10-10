import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumGt
import AFTD.Kb.Physics.PhyslibDistributionNormIteratedFDerivOfRealCLM

/-!
# QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz

Topic: quantum_mechanics   Node: 44358e921ef0

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Parity.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The parity operator on the Schwartz maps is defined as the linear map from `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => ψ (-x)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
/-- The parity operator on the Schwartz maps is defined as the linear map from `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => ψ (-x)`. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  refine (SchwartzMap.compCLM ℂ (g := (fun x => - x : ℝ → ℝ)) ⟨?_, ?_⟩ ?_)
  · fun_prop
  · intro n
    simp only [Real.norm_eq_abs]
    use 1, 1
    intro x
    simp only [pow_one, one_mul]
    rw [show (fun x : ℝ => -x) = -(fun x : ℝ => x) from rfl]
    rw [iteratedFDeriv_neg_apply]
    simp only [norm_neg]
    match n with
    | 0 => simp
    | 1 =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp [ContinuousLinearMap.norm_id]
    | .succ (.succ n) =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Nat.succ_eq_add_one, fderiv_fun_id, Function.comp_apply,
        LinearIsometryEquiv.norm_map, ge_iff_le]
      rw [iteratedFDeriv_const_of_ne]
      simp only [Pi.zero_apply, norm_zero]
      apply add_nonneg
      · exact zero_le_one' ℝ
      · exact abs_nonneg x
      simp
  · simp
    use 1, 1
    intro x
    simp
