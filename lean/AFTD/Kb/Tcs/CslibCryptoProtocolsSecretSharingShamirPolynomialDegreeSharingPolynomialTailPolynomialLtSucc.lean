import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialDegreeSharingPolynomialLtSucc
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialDegreeLt
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ

Topic: cryptography   Node: 7d51895dd9b4

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The coefficient-vector version of `degree_sharingPolynomial_lt_succ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- The coefficient-vector version of `degree_sharingPolynomial_lt_succ`. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
    (secretValue : F) (n : ℕ) (coeffs : Fin n → F) :
    (sharingPolynomial secretValue (tailPolynomial n coeffs)).degree <
      (n + 1 : WithBot ℕ) :=
  degree_sharingPolynomial_lt_succ secretValue (tailPolynomial n coeffs)
    (tailPolynomial_degree_lt n coeffs)
