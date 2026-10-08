import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.shareDist

Topic: cryptography   Node: 806be8d4ee88

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.shareDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The distribution of the full share assignment for one secret.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- The distribution of the full share assignment for one secret. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Scheme.shareDist (scheme : Scheme Secret Randomness Party Share)
    (secret : Secret) : PMF (Party → Share) :=
  scheme.gen.map (fun r => scheme.share r secret)
