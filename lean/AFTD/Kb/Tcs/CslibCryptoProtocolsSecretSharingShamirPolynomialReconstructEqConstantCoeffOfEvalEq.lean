import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstruct

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq

Topic: cryptography   Node: 623e2384e620

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reconstruction recovers the constant coefficient of any low-degree polynomial from its values at distinct points.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
variable {ι : Type*} [Fintype ι] in
/-- Reconstruction recovers the constant coefficient of any low-degree polynomial from its values at distinct points. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq
    {x : ι → F} {p : _root_.Polynomial F}
    (hx : Function.Injective x)
    (hdeg : p.degree < Fintype.card ι) :
    reconstruct x (fun i => p.eval (x i)) = p.constantCoeff := by
  classical
  have hp :
      p = _root_.Lagrange.interpolate Finset.univ x (fun i => p.eval (x i)) :=
    _root_.Lagrange.eq_interpolate
      (s := Finset.univ)
      (v := x)
      hx.injOn
      (by simp [hdeg])
  simpa [reconstruct] using congrArg _root_.Polynomial.constantCoeff hp.symm
