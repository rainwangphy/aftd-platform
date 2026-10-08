import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrectionPolynomialDegreeLt
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrection

Topic: cryptography   Node: e88573462afb

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrection`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrection
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) : Randomness params :=
  _root_.Polynomial.degreeLTEquiv F params.threshold
    ⟨privacyCorrectionPolynomial (F := F) params s secret₀ secret₁,
      _root_.Polynomial.mem_degreeLT.2
        (privacyCorrectionPolynomial_degree_lt (F := F) params s secret₀ secret₁ hcard)⟩
