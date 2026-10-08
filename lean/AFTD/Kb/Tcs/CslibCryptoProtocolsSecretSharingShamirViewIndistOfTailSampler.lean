import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingViewDistOf
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirAuthorized
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirShare
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirViewEqViewAddPrivacyCorrection
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPrivacyCorrection
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailSampler

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.view_indist_of_tailSampler

Topic: cryptography   Node: 7a34c863a694

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.view_indist_of_tailSampler`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Translation-invariant Shamir tail samplers induce secret-independent views for unauthorized coalitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Translation-invariant Shamir tail samplers induce secret-independent views for unauthorized coalitions. -/
theorem Cslib.Crypto.Protocols.SecretSharing.Shamir.view_indist_of_tailSampler (params : Params F Party)
    (sampler : TailSampler params) :
    ∀ (s : Finset Party), ¬ authorized params s → ∀ secret₀ secret₁ : F,
      viewDistOf sampler.gen (share params) s secret₀ =
        viewDistOf sampler.gen (share params) s secret₁ := by
  intro s hs secret₀ secret₁
  have hcard : s.card ≤ params.threshold := by
    have hs' : ¬ params.threshold + 1 ≤ s.card := by
      simpa [authorized] using hs
    exact Nat.lt_succ_iff.mp (Nat.not_le.mp hs')
  unfold viewDistOf
  calc
    PMF.map (fun coeffs : Randomness params =>
        (fun i : s => share params coeffs secret₀ i : s → F)) sampler.gen =
      PMF.map
        (fun coeffs : Randomness params => (fun i : s =>
          share params
            (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
            secret₁ i : s → F)) sampler.gen := by
        congr 1
        funext coeffs
        exact view_eq_view_add_privacyCorrection
          (F := F) params s hcard secret₀ secret₁ coeffs
    _ = PMF.map (fun coeffs : Randomness params =>
          (fun i : s => share params coeffs secret₁ i : s → F))
        (PMF.map
          (fun coeffs => coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
          sampler.gen) := by
          rw [PMF.map_comp]
          rfl
    _ = PMF.map (fun coeffs : Randomness params =>
          (fun i : s => share params coeffs secret₁ i : s → F)) sampler.gen := by
          rw [sampler.map_add_eq_self]
