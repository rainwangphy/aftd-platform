import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.view

Topic: cryptography   Node: e79f9154e786

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.view`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The restricted shares observed by the coalition `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- The restricted shares observed by the coalition `s`. -/
def Cslib.Crypto.Protocols.SecretSharing.Scheme.view (scheme : Scheme Secret Randomness Party Share) (s : Finset Party)
    (r : Randomness) (secret : Secret) : s → Share :=
  fun i => scheme.share r secret i
