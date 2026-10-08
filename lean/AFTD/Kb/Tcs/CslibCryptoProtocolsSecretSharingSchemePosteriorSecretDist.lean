import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDist

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist

Topic: cryptography   Node: e42b8a760e80

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The posterior distribution on secrets after observing the coalition view `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- The posterior distribution on secrets after observing the coalition view `v`. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support) : PMF Secret :=
  Cslib.Probability.PMF.posteriorDist
    (p := secretDist) (f := scheme.viewDist s) v hv
