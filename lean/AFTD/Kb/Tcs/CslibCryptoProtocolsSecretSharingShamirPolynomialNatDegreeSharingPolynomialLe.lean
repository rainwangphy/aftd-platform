import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.natDegree_sharingPolynomial_le

Topic: cryptography   Node: 1886a8c8368b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.natDegree_sharingPolynomial_le`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the tail polynomial has degree `< n`, then the sharing polynomial has natural degree at most `n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- If the tail polynomial has degree `< n`, then the sharing polynomial has natural degree at most `n`. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.natDegree_sharingPolynomial_le (secretValue : F) (tail : _root_.Polynomial F) {n : ℕ}
    (hdeg : tail.degree < n) :
    (sharingPolynomial secretValue tail).natDegree ≤ n := by
  rw [sharingPolynomial]
  refine (_root_.Polynomial.natDegree_add_le _ _).trans ?_
  rw [max_le_iff]
  constructor
  · rw [_root_.Polynomial.natDegree_C]
    exact Nat.zero_le n
  · by_cases htail : tail = 0
    · simp [htail]
    · rw [_root_.Polynomial.natDegree_X_mul htail]
      have htailDegree : tail.natDegree < n := by
        have := hdeg
        rw [_root_.Polynomial.degree_eq_natDegree htail] at this
        exact_mod_cast this
      exact Nat.succ_le_of_lt htailDegree
