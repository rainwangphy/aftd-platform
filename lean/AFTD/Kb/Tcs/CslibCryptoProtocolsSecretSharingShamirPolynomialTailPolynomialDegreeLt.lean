import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_degree_lt

Topic: cryptography   Node: 716780e58b13

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_degree_lt`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`tailPolynomial n coeffs` has degree `< n` by construction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- `tailPolynomial n coeffs` has degree `< n` by construction. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_degree_lt (n : ℕ) (coeffs : Fin n → F) :
    (tailPolynomial (F := F) n coeffs).degree < n :=
  _root_.Polynomial.mem_degreeLT.1
    (((_root_.Polynomial.degreeLTEquiv F n).symm coeffs :
      _root_.Polynomial.degreeLT F n)).2
