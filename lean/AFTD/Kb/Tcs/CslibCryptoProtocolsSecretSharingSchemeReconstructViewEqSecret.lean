import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeView

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.reconstruct_view_eq_secret

Topic: cryptography   Node: 46eb3df83e98

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.reconstruct_view_eq_secret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Authorized coalitions reconstruct the secret from the restricted view.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- Authorized coalitions reconstruct the secret from the restricted view. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Scheme.reconstruct_view_eq_secret
    (scheme : Scheme Secret Randomness Party Share)
    (r : Randomness) (secret : Secret) {s : Finset Party}
    (hs : scheme.authorized s) :
    scheme.reconstruct s (scheme.view s r secret) = secret :=
  scheme.correct r secret s hs
