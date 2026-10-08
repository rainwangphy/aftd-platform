import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyJointDistEq

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.indep_of_ciphertextIndist

Topic: cryptography   Node: 6f5b027e873c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.indep_of_ciphertextIndist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ciphertext indistinguishability implies message-ciphertext independence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Ciphertext indistinguishability implies message-ciphertext independence. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.indep_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist)
    (msgDist : PMF M) (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) =
      msgDist m * scheme.marginalCiphertextDist msgDist c := by
  rw [jointDist_eq]; congr 1
  change scheme.ciphertextDist m c =
    PMF.bind msgDist (fun m' => scheme.ciphertextDist m') c
  rw [PMF.bind_apply]
  conv_rhs => arg 1; ext m'; rw [h m' m]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
