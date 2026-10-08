import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.F

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.coeffTranslate

Topic: cryptography   Node: a6219e55704f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.coeffTranslate`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Crypto.Protocols.SecretSharing.Shamir.coeffTranslate
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.coeffTranslate {params : Params F Party} (δ : Randomness params) :
    Randomness params ≃ Randomness params where
  toFun coeffs := coeffs + δ
  invFun coeffs := coeffs - δ
  left_inv coeffs := by simp
  right_inv coeffs := by simp
