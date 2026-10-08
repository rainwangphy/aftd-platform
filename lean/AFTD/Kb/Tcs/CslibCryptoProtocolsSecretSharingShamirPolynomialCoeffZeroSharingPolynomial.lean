import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.coeff_zero_sharingPolynomial

Topic: cryptography   Node: a2ed799a088a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.coeff_zero_sharingPolynomial`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.coeff_zero_sharingPolynomial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.coeff_zero_sharingPolynomial (secretValue : F) (tail : _root_.Polynomial F) :
    (sharingPolynomial secretValue tail).coeff 0 = secretValue := by
  simp [sharingPolynomial]
