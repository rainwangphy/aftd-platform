import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncSchemeMarginalCiphertextDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsPerfectSecrecyEncScheme
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDist

/-!
# Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist

Topic: cryptography   Node: c4506e9819cc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The posterior message distribution `Pr[M | C = c]` as a probability distribution, given a message prior and a ciphertext in the support of the marginal distribution.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {M K C : Type u} in
/-- The posterior message distribution `Pr[M | C = c]` as a probability distribution, given a message prior and a ciphertext in the support of the marginal distribution. -/
noncomputable def Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) : PMF M :=
  Cslib.Probability.PMF.posteriorDist msgDist scheme.ciphertextDist c hc
