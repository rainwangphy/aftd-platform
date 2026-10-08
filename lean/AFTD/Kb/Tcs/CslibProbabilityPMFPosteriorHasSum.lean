import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairTsumFst
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Probability.PMF.posterior_hasSum

Topic: randomness   Node: bf7475cd5aee

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.posterior_hasSum`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Posterior probabilities `joint(a, b) / marginal(b)` sum to 1 when `b` is in the support of the marginal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- Posterior probabilities `joint(a, b) / marginal(b)` sum to 1 when `b` is in the support of the marginal. -/
theorem Cslib.Probability.PMF.posterior_hasSum (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) :
    HasSum (fun a =>
      (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
        (p.bind f) b) 1 := by
  have hne := (PMF.mem_support_iff _ _).mp hb
  have hne_top := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one (p.bind f) b)
  have : ∑' a, (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
      (p.bind f) b = 1 := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, bind_pair_tsum_fst]
    exact ENNReal.mul_inv_cancel hne hne_top
  exact this ▸ ENNReal.summable.hasSum
