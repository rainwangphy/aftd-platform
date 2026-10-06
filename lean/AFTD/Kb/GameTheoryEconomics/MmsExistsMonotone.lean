import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.IsMonotoneValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mms_exists_monotone

Topic: fair_division   Node: 1f83757426b8

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Sec. 1 (MMS allocations for monotone valuations over goods)

Every instance with n agents and m goods, in which every agent has a monotone valuation v_i with v_i(∅) = 0, has an MMS allocation: an allocation A with v_i(A_i) ≥ MMS(M, v_i, n) for every agent i.
-/

/-- MMS allocations always exist for `n` agents and `m` goods with monotone valuations: for every profile of monotone valuations with `v i ∅ = 0`, some allocation gives every agent at least her maximin share. -/
def mms_exists_monotone (n m : ℕ) : Prop :=
  ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, is_monotone_valuation (v i) ∧ v i ∅ = 0) →
    ∃ σ : Fin m → Fin n, ∀ i, maximin_share (v i) n ≤ v i (bundle_of σ i)
