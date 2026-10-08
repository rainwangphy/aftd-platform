import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyJointDistTsumFst
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePosteriorMsgDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePosteriorMsgDistApply
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_iff_indep

Topic: cryptography   Node: 59a7f530e8e2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_iff_indep`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Perfect secrecy is equivalent to message-ciphertext independence. The two formulations are related by multiplying/dividing by `marginal(c)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Perfect secrecy is equivalent to message-ciphertext independence. The two formulations are related by multiplying/dividing by `marginal(c)`. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_iff_indep (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ (msgDist : PMF M) (m : M) (c : C),
      scheme.jointDist msgDist (m, c) =
        msgDist m * scheme.marginalCiphertextDist msgDist c := by
  constructor
  · intro h msgDist m c
    by_cases hc : (scheme.marginalCiphertextDist msgDist) c = 0
    · have := ENNReal.tsum_eq_zero.mp
        ((jointDist_tsum_fst scheme msgDist c).trans hc) m
      rw [this, hc, mul_zero]
    · have hne_top := ne_top_of_le_ne_top one_ne_top
        (PMF.coe_le_one (scheme.marginalCiphertextDist msgDist) c)
      have := DFunLike.congr_fun (h msgDist c ((PMF.mem_support_iff _ _).mpr hc)) m
      simp only [EncScheme.posteriorMsgDist_apply] at this
      rw [← this, ENNReal.div_mul_cancel hc hne_top]
  · intro h msgDist c hc; ext m
    simp only [EncScheme.posteriorMsgDist_apply]
    rw [h msgDist m c, ENNReal.mul_div_cancel_right
      ((PMF.mem_support_iff _ _).mp hc)
      (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one _ c))]
