import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPointsInjOnSubtype
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt

Topic: cryptography   Node: 68a6e6d83567

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) (hcard : s.card ≤ params.threshold) :
    (privacyCorrectionPolynomial (F := F) params s secret₀ secret₁).degree <
      params.threshold := by
  classical
  refine lt_of_lt_of_le
    (_root_.Lagrange.degree_interpolate_lt
      (s := s.attach)
      (v := fun i : s => params.point i)
      (r := fun i : s => (secret₀ - secret₁) / params.point i)
      (points_injOn_subtype (F := F) params s))
    ?_
  simp [hcard]
