import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm

/-!
# online_ef1_approximation_ratio

Topic: fair_division   Node: 1f6e0f69c30f

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 5

For n agents, the online EF1 approximation ratio is the supremum of all ratios alpha in [0, 1] for which there exists a deterministic online algorithm guaranteeing an alpha-EF1 allocation under exact frequency predictions.
-/

/-- The supremum of approximation ratios α ∈ [0, 1] guaranteed by a deterministic online algorithm for n agents under exact frequency predictions. -/
noncomputable def online_ef1_approximation_ratio (n : ℕ) : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧ has_online_alpha_ef1_algorithm n α}
