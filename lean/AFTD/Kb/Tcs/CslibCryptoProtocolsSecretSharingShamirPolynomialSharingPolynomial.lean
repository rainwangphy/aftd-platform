import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial

Topic: cryptography   Node: 407b33462747

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir/Polynomial.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard Shamir sharing polynomial `s + X * q(X)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F : Type*} [Field F] in
/-- The standard Shamir sharing polynomial `s + X * q(X)`. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial (secretValue : F) (tail : _root_.Polynomial F) : _root_.Polynomial F :=
  _root_.Polynomial.C secretValue + _root_.Polynomial.X * tail
