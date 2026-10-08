import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairTsumFst
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_tsum_fst

Topic: cryptography   Node: c4f50470054a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_tsum_fst`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Summing the joint distribution over messages gives the marginal ciphertext distribution.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Summing the joint distribution over messages gives the marginal ciphertext distribution. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_tsum_fst (scheme : EncScheme M K C) (msgDist : PMF M) (c : C) :
    ∑' m, scheme.jointDist msgDist (m, c) = scheme.marginalCiphertextDist msgDist c :=
  Cslib.Probability.PMF.bind_pair_tsum_fst msgDist scheme.ciphertextDist c
