import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct

Topic: cryptography   Node: a6986e41b3d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reconstruct the secret from finitely indexed share values by interpolating the unique low-degree polynomial that matches them.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
variable {ι : Type*} [Fintype ι] in
/-- Reconstruct the secret from finitely indexed share values by interpolating the unique low-degree polynomial that matches them. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct (x σ : ι → F) : F :=
  by
    classical
    exact (_root_.Lagrange.interpolate Finset.univ x σ).constantCoeff
