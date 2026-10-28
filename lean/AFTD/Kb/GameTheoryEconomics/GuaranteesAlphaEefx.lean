import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOverestimatePrediction
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxAllocation
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# guarantees_alpha_eefx

Topic: fair_division   Node: 35099e7f6b04

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 6.1

An algorithm alg guarantees alpha-EEFX for n agents under error factor ρ if for every m : ℕ, all nonnegative valuations v and all predictions a_hat that are overestimates with factor ρ, the allocation alg m a_hat v is alpha-EEFX.
-/

/-- An algorithm guarantees alpha-EEFX under error factor rho if its allocations are alpha-EEFX for all valid instances. -/
def guarantees_alpha_eefx (n : ℕ) (alg : ∀ m : ℕ, (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n))
    (ρ α : ℝ) : Prop :=
  ∀ (m : ℕ) (v a_hat : Fin n → Fin m → ℝ),
    (∀ i g, 0 ≤ v i g) →
    is_overestimate_prediction ρ v a_hat →
    is_alpha_eefx_allocation (fun i => additive_valuation (v i)) α (alg m a_hat v)
