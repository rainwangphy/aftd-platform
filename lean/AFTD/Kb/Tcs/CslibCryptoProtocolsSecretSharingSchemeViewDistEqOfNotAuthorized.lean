import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewDist

/-!
# Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist_eq_of_not_authorized

Topic: cryptography   Node: f4670cb6be09

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist_eq_of_not_authorized`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unauthorized coalitions receive secret-independent view distributions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Secret Randomness Party Share : Type*} in
/-- Unauthorized coalitions receive secret-independent view distributions. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist_eq_of_not_authorized
    (scheme : Scheme Secret Randomness Party Share)
    {s : Finset Party} (hs : ¬ scheme.authorized s)
    (secret₀ secret₁ : Secret) :
    scheme.viewDist s secret₀ = scheme.viewDist s secret₁ := by
  unfold viewDist
  exact scheme.view_indist s hs secret₀ secret₁
