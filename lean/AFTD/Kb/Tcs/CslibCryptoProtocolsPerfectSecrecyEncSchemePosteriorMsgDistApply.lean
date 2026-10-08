import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeJointDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePosteriorMsgDist

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply

Topic: cryptography   Node: b14ebdc771b3

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
@[simp]
theorem Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) (m : M) :
    scheme.posteriorMsgDist msgDist c hc m =
      scheme.jointDist msgDist (m, c) / scheme.marginalCiphertextDist msgDist c :=
  rfl
