import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1Goods
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm
import AFTD.Kb.GameTheoryEconomics.IsExactPrediction

/-!
# has_online_alpha_ef1_algorithm

Topic: fair_division   Node: cb97ca7f3574

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 2, Sec. 5

There exists a deterministic online algorithm for n agents that, for any number of goods m, given exact frequency predictions a_hat and arriving nonnegative additive valuations v, produces an alpha-EF1 allocation.
-/

/-- Existence of a deterministic online algorithm guaranteeing an α-EF1 allocation for n agents given exact frequency predictions. -/
def has_online_alpha_ef1_algorithm (n : ℕ) (α : ℝ) : Prop :=
  ∃ (alg : ∀ m : ℕ, (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n)),
    is_online_algorithm n alg ∧
    ∀ (m : ℕ) (v a_hat : Fin n → Fin m → ℝ),
      (∀ i g, 0 ≤ v i g) →
      is_exact_prediction v a_hat →
      is_alpha_ef1_goods v α (alg m a_hat v)
