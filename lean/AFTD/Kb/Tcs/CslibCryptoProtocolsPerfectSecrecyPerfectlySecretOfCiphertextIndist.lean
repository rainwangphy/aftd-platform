import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextIndist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePerfectlySecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyPerfectlySecretIffIndep
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyIndepOfCiphertextIndist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_of_ciphertextIndist

Topic: cryptography   Node: 336bac7a43d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_of_ciphertextIndist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ciphertext indistinguishability implies perfect secrecy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- Ciphertext indistinguishability implies perfect secrecy. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.perfectlySecret_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist) :
    scheme.PerfectlySecret :=
  (perfectlySecret_iff_indep scheme).mpr (fun msgDist m c =>
    indep_of_ciphertextIndist scheme h msgDist m c)
