import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.TailSampler

Topic: cryptography   Node: ff158e2ff1e4

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.TailSampler`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A sampler on Shamir tail coefficients is privacy-compatible when its distribution is invariant under translation by any coefficient vector. This is the exact symmetry needed in the privacy proof.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- A sampler on Shamir tail coefficients is privacy-compatible when its distribution is invariant under translation by any coefficient vector. This is the exact symmetry needed in the privacy proof. -/
structure Cslib.Crypto.Protocols.SecretSharing.Shamir.TailSampler (params : Params F Party) where
  /-- The underlying coefficient distribution. -/
  gen : PMF (Randomness params)
  /-- Translating the coefficients does not change the distribution. -/
  map_add_eq_self : ∀ δ : Randomness params, gen.map (fun coeffs => coeffs + δ) = gen
