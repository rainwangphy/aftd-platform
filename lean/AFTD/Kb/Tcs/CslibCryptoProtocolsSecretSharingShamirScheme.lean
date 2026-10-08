import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirSchemeWith
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirUniformTailSampler
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme

Topic: cryptography   Node: d13fe4e6ea40

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical finite-field Shamir scheme with uniformly sampled tail coefficients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- The canonical finite-field Shamir scheme with uniformly sampled tail coefficients. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme (params : Params F Party)
    [Fintype F] [Nonempty F] :
    SecretSharing.Scheme F (Randomness params) Party F :=
  schemeWith params (uniformTailSampler params)
