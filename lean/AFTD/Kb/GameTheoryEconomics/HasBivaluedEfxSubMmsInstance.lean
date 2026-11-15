import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# has_bivalued_efx_sub_mms_instance

Topic: fair_division   Node: 329670b1cd44

Provenance: original. Related work: arXiv:2611.15582

Given natural numbers n, R, and d, there exists a finite additive instance with n agents where each item value is either 1 or the natural number R, admitting a complete EFX allocation σ and an agent i whose bundle has value strictly less than her 1-out-of-d maximin share.
-/

/-- Predicate that an n-agent additive instance with item values in {1, R} admits a complete EFX allocation where some agent receives strictly less than her 1-out-of-d maximin share. -/
def has_bivalued_efx_sub_mms_instance (n : ℕ) (R : ℕ) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (i : Fin n),
    (∀ j g, u j g = 1 ∨ u j g = (R : ℝ)) ∧
    is_efx_goods u σ ∧
    additive_valuation (u i) (bundle_of σ i) < maximin_share (additive_valuation (u i)) d
