import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWithAuthorizedIff
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff

Topic: cryptography   Node: b1a665a165cd

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff (params : Params F Party)
    [Fintype F] [Nonempty F] (s : Finset Party) :
    (scheme params).authorized s ↔ params.threshold + 1 ≤ s.card :=
  Iff.rfl
