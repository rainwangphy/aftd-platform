import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailSampler
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWith
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeView
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeReconstructViewEqSecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWithAuthorizedIff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWithShareEq
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret

Topic: cryptography   Node: e66d95d695fb

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any authorized coalition reconstructs the secret from the shares it sees.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Any authorized coalition reconstructs the secret from the shares it sees. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret
    (params : Params F Party) (sampler : TailSampler params)
    (coeffs : Randomness params) (secretValue : F) {s : Finset Party}
    (hs : (schemeWith params sampler).authorized s) :
    (schemeWith params sampler).reconstruct s
      ((schemeWith params sampler).view s coeffs secretValue) = secretValue :=
  SecretSharing.Scheme.reconstruct_view_eq_secret
    (schemeWith params sampler) coeffs secretValue hs
