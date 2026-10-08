import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirCoeffTranslate
import AFTD.Kb.Tcs.CslibProbabilityPMFUniformOfFintypeMapEquiv
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailSampler

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.uniformTailSampler

Topic: cryptography   Node: 6c6cd2fae6b6

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.uniformTailSampler`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform tail coefficients form the canonical privacy-compatible sampler.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Uniform tail coefficients form the canonical privacy-compatible sampler. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.uniformTailSampler (params : Params F Party)
    [Fintype F] [Nonempty F] : TailSampler params where
  gen := PMF.uniformOfFintype (Randomness params)
  map_add_eq_self δ := by
    simpa [coeffTranslate] using
      (Cslib.Probability.PMF.uniformOfFintype_map_equiv
        (coeffTranslate (params := params) δ))
