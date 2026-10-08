import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairApply
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDist

/-!
# Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist

Topic: randomness   Node: 0fdd4bfd2dd1

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the output distribution of a channel does not depend on the input, then conditioning on any output with positive probability leaves the prior unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- If the output distribution of a channel does not depend on the input, then conditioning on any output with positive probability leaves the prior unchanged. -/
theorem Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist (p : PMF α) (f : α → PMF β)
    (h : ∀ a₀ a₁ : α, f a₀ = f a₁)
    (b : β) (hb : b ∈ (p.bind f).support) :
    posteriorDist p f b hb = p := by
  ext a
  rw [posteriorDist_apply, bind_pair_apply, PMF.bind_apply]
  have hf : ∀ a', f a' b = f a b := fun a' => by rw [h a' a]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hb' : (p.bind f) b ≠ 0 := (PMF.mem_support_iff _ _).mp hb
  have hmarg : (p.bind f) b = f a b := by
    rw [PMF.bind_apply]
    simp_rw [hf]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact ENNReal.mul_div_cancel_right (hmarg ▸ hb')
    (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _))
