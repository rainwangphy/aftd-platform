import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingViewDistOf

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist

Topic: cryptography   Node: 4a8eacb23202

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The view distribution induced on the coalition `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- The view distribution induced on the coalition `s`. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secret : Secret) : PMF (s → Share) :=
  viewDistOf scheme.gen scheme.share s secret
