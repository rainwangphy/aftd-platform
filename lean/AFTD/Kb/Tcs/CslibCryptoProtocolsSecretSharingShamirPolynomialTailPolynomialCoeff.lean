import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_coeff

Topic: cryptography   Node: 0122e5cff0e4

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_coeff`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_coeff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_coeff (n : ℕ) (coeffs : Fin n → F) (i : Fin n) :
    (tailPolynomial (F := F) n coeffs).coeff i = coeffs i := by
  have h := congrFun
    (LinearEquiv.apply_symm_apply (_root_.Polynomial.degreeLTEquiv F n) coeffs) i
  simpa [tailPolynomial, _root_.Polynomial.degreeLTEquiv] using h
