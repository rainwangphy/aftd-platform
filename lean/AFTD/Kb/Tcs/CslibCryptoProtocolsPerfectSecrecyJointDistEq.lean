import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairApply

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_eq

Topic: cryptography   Node: 7a57457b50ae

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_eq`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Internal/PerfectSecrecy.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The joint distribution at `(m, c)` equals `msgDist m * ciphertextDist m c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open PMF ENNReal in
universe u in
variable {M K C : Type u} in
/-- The joint distribution at `(m, c)` equals `msgDist m * ciphertextDist m c`. -/
theorem Cslib.Crypto.Protocols.PerfectSecrecy.jointDist_eq (scheme : EncScheme M K C) (msgDist : PMF M)
    (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) = msgDist m * scheme.ciphertextDist m c :=
  Cslib.Probability.PMF.bind_pair_apply msgDist scheme.ciphertextDist m c
