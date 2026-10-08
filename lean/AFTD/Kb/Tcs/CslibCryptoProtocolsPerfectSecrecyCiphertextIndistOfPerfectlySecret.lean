import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyJointDistEq
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyPerfectlySecretIffIndep
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.ciphertextIndist_of_perfectlySecret

Topic: cryptography   Node: 0304ccad0581

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.ciphertextIndist_of_perfectlySecret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Perfect secrecy implies ciphertext indistinguishability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Perfect secrecy implies ciphertext indistinguishability. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.ciphertextIndist_of_perfectlySecret (scheme : EncScheme M K C)
    (h : scheme.PerfectlySecret) :
    scheme.CiphertextIndist := by
  classical
  rw [perfectlySecret_iff_indep] at h
  intro m₀ m₁; ext c
  have hs : ({m₀, m₁} : Finset M).Nonempty := ⟨m₀, Finset.mem_insert_self ..⟩
  set μ := PMF.uniformOfFinset _ hs
  suffices key : ∀ m ∈ ({m₀, m₁} : Finset M),
      scheme.ciphertextDist m c = scheme.marginalCiphertextDist μ c by
    exact (key m₀ (by simp)).trans (key m₁ (by simp)).symm
  intro m hm
  have hne := (PMF.mem_support_uniformOfFinset_iff hs m).mpr hm
  have hne_top := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one μ m)
  exact (ENNReal.mul_right_inj hne hne_top).mp (by rw [← jointDist_eq]; exact h μ m c)
