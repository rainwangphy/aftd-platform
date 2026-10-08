import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstructEqConstantCoeffOfEvalEq
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialConstantCoeffSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstruct
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret

Topic: cryptography   Node: 1aab79c7fe8c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reconstruction succeeds on the values of a Shamir sharing polynomial once the finite index type is large enough.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
variable {ι : Type*} [Fintype ι] in
/-- Reconstruction succeeds on the values of a Shamir sharing polynomial once the finite index type is large enough. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret
    {x : ι → F} {secretValue : F} {tail : _root_.Polynomial F}
    (hx : Function.Injective x)
    (hdeg : (sharingPolynomial secretValue tail).degree < Fintype.card ι) :
    reconstruct x
      (fun i => (sharingPolynomial secretValue tail).eval (x i)) = secretValue := by
  rw [reconstruct_eq_constantCoeff_of_eval_eq
    (p := sharingPolynomial secretValue tail) hx hdeg]
  exact constantCoeff_sharingPolynomial secretValue tail
