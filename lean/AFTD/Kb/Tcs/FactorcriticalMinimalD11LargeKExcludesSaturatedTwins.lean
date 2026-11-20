import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.MinimalFactorcriticalSaturatedTwinsRefinedQuadraticBound

/-!
# factorcritical_minimal_d11_large_k_excludes_saturated_twins

Topic: graphs   Node: 47ec45a8cdd3

Provenance: helper lemma. OP-1957 small-complement-degree saturated-twin exclusion.

At d=11 the displayed saturated twins are impossible when k≥10.
-/

theorem factorcritical_minimal_d11_large_k_excludes_saturated_twins
    (k : ℕ) (hk : 10 ≤ k) (H : SimpleGraph (Fin (2*k+11+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (hmin : is_minimally_k_extendable Hᶜ k)
    (x y : Fin (2*k+11+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = 11) (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) : False := by
  obtain ⟨t,hinc,hwalk⟩ := minimal_factorcritical_saturated_twins_refined_quadratic_bound
    k 11 H hcrit hmin x y hxy hxdeg hmax htwin
  norm_num at hinc hwalk
  omega
