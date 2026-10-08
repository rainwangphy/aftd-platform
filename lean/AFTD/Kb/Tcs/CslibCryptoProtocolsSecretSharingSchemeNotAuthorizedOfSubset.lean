import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset

Topic: cryptography   Node: 11d80a8ed459

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any sub-coalition of an unauthorized coalition is unauthorized as well.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- Any sub-coalition of an unauthorized coalition is unauthorized as well. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset
    (scheme : Scheme Secret Randomness Party Share)
    {s t : Finset Party} (hst : s ⊆ t)
    (ht : ¬ scheme.authorized t) :
    ¬ scheme.authorized s := by
  intro hs
  exact ht (scheme.authorized_mono hst hs)
