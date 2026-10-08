import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemePosteriorMsgDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret

Topic: cryptography   Node: b1e9c2038bf8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An encryption scheme is perfectly secret if the posterior message distribution equals the prior for every ciphertext with positive probability ([KatzLindell2020], Definition 2.3).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- An encryption scheme is perfectly secret if the posterior message distribution equals the prior for every ciphertext with positive probability ([KatzLindell2020], Definition 2.3). -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.PerfectlySecret (scheme : EncScheme M K C) : Prop :=
  ∀ (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support),
    scheme.posteriorMsgDist msgDist c hc = msgDist
