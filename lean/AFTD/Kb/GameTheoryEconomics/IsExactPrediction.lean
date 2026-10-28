import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SortedTuple

/-!
# is_exact_prediction

Topic: fair_division   Node: 15862b08f6a2

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 6

Frequency predictions a_hat : Fin n → Fin m → ℝ are exact for valuations v : Fin n → Fin m → ℝ if for every agent i : Fin n, the sorted tuple of a_hat i equals the sorted tuple of v i.
-/

/-- Predictions a_hat are exact for v if sorted_tuple (a_hat i) = sorted_tuple (v i) for all agents i. -/
def is_exact_prediction {m n : ℕ} (v : Fin n → Fin m → ℝ) (a_hat : Fin n → Fin m → ℝ) : Prop :=
  ∀ i : Fin n, sorted_tuple (a_hat i) = sorted_tuple (v i)
