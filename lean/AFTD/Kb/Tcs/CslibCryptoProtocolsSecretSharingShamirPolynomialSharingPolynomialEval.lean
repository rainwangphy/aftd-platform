import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial_eval

Topic: cryptography   Node: d15db7901a64

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial_eval`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial_eval
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
@[simp]
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial_eval (secretValue x : F) (tail : _root_.Polynomial F) :
    (sharingPolynomial secretValue tail).eval x = secretValue + x * tail.eval x := by
  simp [sharingPolynomial, mul_comm]
