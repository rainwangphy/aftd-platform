import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialNatDegreeSharingPolynomialLe
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_lt_succ

Topic: cryptography   Node: ee3c8026c11d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_lt_succ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the tail polynomial has degree `< n`, then the sharing polynomial has degree `< n + 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- If the tail polynomial has degree `< n`, then the sharing polynomial has degree `< n + 1`. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_lt_succ (secretValue : F) (tail : _root_.Polynomial F) {n : ℕ}
    (hdeg : tail.degree < n) :
    (sharingPolynomial secretValue tail).degree < (n + 1 : WithBot ℕ) := by
  by_cases hsharing : sharingPolynomial secretValue tail = 0
  · simp [hsharing]
  · rw [_root_.Polynomial.degree_eq_natDegree hsharing]
    exact_mod_cast Nat.lt_succ_of_le (natDegree_sharingPolynomial_le secretValue tail hdeg)
