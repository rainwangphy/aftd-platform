import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrection
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection

Topic: cryptography   Node: 51f899362298

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) :
    Polynomial.tailPolynomial (F := F) params.threshold
        (privacyCorrection (F := F) params s hcard secret₀ secret₁) =
      privacyCorrectionPolynomial (F := F) params s secret₀ secret₁ := by
  simp [privacyCorrection, Polynomial.tailPolynomial]
