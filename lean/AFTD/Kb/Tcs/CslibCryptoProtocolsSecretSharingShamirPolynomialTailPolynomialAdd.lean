import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_add

Topic: cryptography   Node: 6272cfaec224

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_add`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`tailPolynomial` is additive in its coefficient vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- `tailPolynomial` is additive in its coefficient vector. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_add (n : ℕ) (a b : Fin n → F) :
    tailPolynomial (F := F) n (a + b) = tailPolynomial n a + tailPolynomial n b := by
  simp [tailPolynomial]
