import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWith
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWithAuthorizedIff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirShare
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailSampler

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_share_eq

Topic: cryptography   Node: 50becb1966ea

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_share_eq`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_share_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_share_eq (params : Params F Party)
    (sampler : TailSampler params) (coeffs : Randomness params)
    (secretValue : F) (i : Party) :
    (schemeWith params sampler).share coeffs secretValue i =
      share params coeffs secretValue i :=
  rfl
