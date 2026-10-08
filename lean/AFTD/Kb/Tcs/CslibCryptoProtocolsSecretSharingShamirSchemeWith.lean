import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomialCoeff
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialTailPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstructSharingPolynomialEqSecret
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomial
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirAuthorized
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirViewIndistOfTailSampler
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialDegreeSharingPolynomialTailPolynomialLtSucc
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingScheme
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirRandomness
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirParams
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirShare
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialReconstruct
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingSchemeViewApply
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirPolynomialSharingPolynomialEval
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirReconstruct
import AFTD.Kb.Tcs.CslibCryptoProtocolsSecretSharingShamirTailSampler

/-!
# Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith

Topic: cryptography   Node: 3cfeeda2b7df

Provenance: formalization of a published result. Source: CSLib, `Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Crypto/Protocols/SecretSharing/Shamir.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shamir's scheme built from a privacy-compatible tail sampler.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {F Party : Type*} [Field F] [Fintype Party] in
/-- Shamir's scheme built from a privacy-compatible tail sampler. -/
noncomputable def Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith (params : Params F Party) (sampler : TailSampler params)
    :
    SecretSharing.Scheme F (Randomness params) Party F :=
  { gen := sampler.gen
    share := share params
    reconstruct := reconstruct params
    authorized := authorized params
    authorized_mono := by
      intro s u hsu hs
      exact le_trans hs (Finset.card_le_card hsu)
    correct := by
      intro coeffs secretValue s hs
      have hdeg₀ :
          (Polynomial.sharingPolynomial secretValue
              (Polynomial.tailPolynomial params.threshold coeffs)).degree <
            (params.threshold + 1 : WithBot ℕ) :=
        Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
          secretValue params.threshold coeffs
      have hdeg :
          (Polynomial.sharingPolynomial secretValue
              (Polynomial.tailPolynomial params.threshold coeffs)).degree <
            Fintype.card s := by
        simp [(lt_of_lt_of_le hdeg₀ (by exact_mod_cast hs) :
          (Polynomial.sharingPolynomial secretValue
            (Polynomial.tailPolynomial params.threshold coeffs)).degree <
              s.card)]
      have hx : Function.Injective (fun i : s => params.point i) := by
        intro i j hij
        exact Subtype.ext (params.point_injective hij)
      simpa [share, reconstruct] using
        Polynomial.reconstruct_sharingPolynomial_eq_secret
          (x := fun i : s => params.point i)
          (secretValue := secretValue)
          (tail := Polynomial.tailPolynomial params.threshold coeffs)
          hx
          hdeg
    view_indist := view_indist_of_tailSampler params sampler }
