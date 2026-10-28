import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SortedTuple

/-!
# is_overestimate_prediction

Topic: fair_division   Node: 0a3efaceb03e

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 6.1

Predictions a_hat : Fin n → Fin m → ℝ are overestimates of valuations v : Fin n → Fin m → ℝ with error factor ρ if for every agent i : Fin n and rank r : Fin m, sorted_tuple (v i) r ≤ sorted_tuple (a_hat i) r and sorted_tuple (a_hat i) r ≤ ρ * sorted_tuple (v i) r.
-/

/-- Predictions a_hat are overestimates of v with error factor rho if sorted true values <= sorted predicted values <= rho * sorted true values. -/
def is_overestimate_prediction {m n : ℕ} (ρ : ℝ) (v : Fin n → Fin m → ℝ) (a_hat : Fin n → Fin m → ℝ) : Prop :=
  ∀ (i : Fin n) (r : Fin m),
    sorted_tuple (v i) r ≤ sorted_tuple (a_hat i) r ∧ sorted_tuple (a_hat i) r ≤ ρ * sorted_tuple (v i) r
