import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailPolynomialPrivacyCorrection
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialAdd
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirShare
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrection
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomial

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection

Topic: cryptography   Node: 9e7b16020f4a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) (coeffs : Randomness params) :
    (fun i : s => share params coeffs secret₀ i) =
      (fun i : s =>
        share params
          (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
          secret₁ i) := by
  ext i
  unfold share
  rw [Polynomial.sharingPolynomial_eval, Polynomial.sharingPolynomial_eval]
  rw [Polynomial.tailPolynomial_add, _root_.Polynomial.eval_add, tailPolynomial_privacyCorrection]
  rw [privacyCorrectionPolynomial_eval (F := F) params s secret₀ secret₁ i]
  field_simp [params.point_nonzero i]
  ring
