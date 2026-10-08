import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemePosteriorSecretDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.PerfectlyPrivate

Topic: cryptography   Node: 2ee284c6c7e4

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.PerfectlyPrivate`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Perfect privacy for unauthorized coalitions: conditioning on a view does not change the prior on secrets.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- Perfect privacy for unauthorized coalitions: conditioning on a view does not change the prior on secrets. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Scheme.PerfectlyPrivate (scheme : Scheme Secret Randomness Party Share) : Prop :=
  ∀ (s : Finset Party) (_hs : ¬ scheme.authorized s)
    (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support),
      scheme.posteriorSecretDist s secretDist v hv = secretDist
