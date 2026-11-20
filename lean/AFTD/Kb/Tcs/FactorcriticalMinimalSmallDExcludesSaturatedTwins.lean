import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.MinimalFactorcriticalSaturatedTwinsStrictQuadraticBound

/-!
# factorcritical_minimal_small_d_excludes_saturated_twins

Topic: graphs   Node: 90ab860dbe4f

Provenance: helper lemma. OP-1957 small-complement-degree saturated-twin exclusion.

In the conjecture order range, the displayed saturated twins are impossible when d≤9.
-/

theorem factorcritical_minimal_small_d_excludes_saturated_twins
    (k d : ℕ) (hd : d ≤ 9) (horder : d+3 ≤ 2*k)
    (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (hmin : is_minimally_k_extendable Hᶜ k)
    (x y : Fin (2*k+d+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) : False := by
  have hb := minimal_factorcritical_saturated_twins_strict_quadratic_bound
    k d H hcrit hmin x y hxy hxdeg hmax htwin
  interval_cases d <;> norm_num at hb <;> omega
