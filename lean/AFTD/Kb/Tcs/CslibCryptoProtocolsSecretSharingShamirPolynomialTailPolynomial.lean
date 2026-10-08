import AFTD.Prelude

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial

Topic: cryptography   Node: 161da606f4c9

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The tail polynomial determined by the first `n` coefficients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- The tail polynomial determined by the first `n` coefficients. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial (n : ℕ) (coeffs : Fin n → F) : _root_.Polynomial F :=
  ↑((_root_.Polynomial.degreeLTEquiv F n).symm coeffs)
