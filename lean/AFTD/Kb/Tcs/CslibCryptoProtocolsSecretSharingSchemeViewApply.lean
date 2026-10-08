import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeView

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.view_apply

Topic: cryptography   Node: c375535aebdc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.view_apply`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Scheme.view_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Scheme.view_apply (scheme : Scheme Secret Randomness Party Share) (s : Finset Party)
    (r : Randomness) (secret : Secret) (i : s) :
    scheme.view s r secret i = scheme.share r secret i :=
  rfl
