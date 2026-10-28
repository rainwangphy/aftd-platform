import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsExactPrediction
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxAllocation
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_consistent_algorithm

Topic: fair_division   Node: 287540fe4252

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 6

An online algorithm alg for n agents is consistent if for every m : ℕ and all nonnegative valuations v and predictions a_hat with exact predictions, the allocation alg m a_hat v is 1-EEFX.
-/

/-- An algorithm alg is consistent if it returns an EEFX allocation whenever predictions are exact. -/
def is_consistent_algorithm (n : ℕ) (alg : ∀ m : ℕ, (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n)) : Prop :=
  ∀ (m : ℕ) (v a_hat : Fin n → Fin m → ℝ),
    (∀ i g, 0 ≤ v i g) →
    is_exact_prediction v a_hat →
    is_alpha_eefx_allocation (fun i => additive_valuation (v i)) 1 (alg m a_hat v)
