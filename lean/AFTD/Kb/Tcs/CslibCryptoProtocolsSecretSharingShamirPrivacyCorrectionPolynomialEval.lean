import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPointsInjOnSubtype
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_eval

Topic: cryptography   Node: 35fafe0fd3af

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_eval`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_eval
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_eval
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) (i : s) :
    (privacyCorrectionPolynomial (F := F) params s secret₀ secret₁).eval (params.point i) =
      (secret₀ - secret₁) / params.point i := by
  classical
  simpa using!
    (_root_.Lagrange.eval_interpolate_at_node
      (s := s.attach)
      (v := fun j : s => params.point j)
      (r := fun j : s => (secret₀ - secret₁) / params.point j)
      (points_injOn_subtype (F := F) params s)
      (by simp))
