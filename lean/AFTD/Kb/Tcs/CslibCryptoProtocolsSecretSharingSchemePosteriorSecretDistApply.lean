import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewDist
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemePosteriorSecretDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply

Topic: cryptography   Node: 849c08fec66c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support) (secret : Secret) :
    scheme.posteriorSecretDist s secretDist v hv secret =
      (secretDist.bind fun secret' =>
        (scheme.viewDist s secret').bind fun v' => PMF.pure (secret', v')) (secret, v) /
        (secretDist.bind (scheme.viewDist s)) v :=
  rfl
