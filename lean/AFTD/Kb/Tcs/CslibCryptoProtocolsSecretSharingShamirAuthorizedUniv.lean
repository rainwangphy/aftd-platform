import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirAuthorized
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized_univ

Topic: cryptography   Node: 0dc4a89999dc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized_univ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Because `params.threshold < |Party|`, the full party set can always reconstruct the secret.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Because `params.threshold < |Party|`, the full party set can always reconstruct the secret. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized_univ {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party) :
    authorized params (Finset.univ : Finset Party) := by
  simpa [authorized] using Nat.succ_le_of_lt params.threshold_lt_card
