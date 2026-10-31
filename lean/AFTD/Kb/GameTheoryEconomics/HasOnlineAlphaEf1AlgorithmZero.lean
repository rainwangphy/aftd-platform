import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsExactPrediction
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1Goods

/-!
# has_online_alpha_ef1_algorithm_zero

Topic: fair_division   Node: 898acb59efa4

Provenance: helper lemma. step towards op561_exists_online_algorithm_gt_sqrt5

For any positive number of agents n, there exists a deterministic online algorithm guaranteeing a 0-EF1 allocation under exact frequency predictions.
-/

/-- For any positive number of agents n, there exists a deterministic online algorithm guaranteeing a 0-EF1 allocation under exact frequency predictions. -/
theorem has_online_alpha_ef1_algorithm_zero (n : ℕ) [NeZero n] :
    has_online_alpha_ef1_algorithm n 0 := by
  use fun m _ _ _ => 0
  constructor
  · intro m a_hat v v' t ht
    rfl
  · intro m v a_hat h_nonneg h_exact i j hij h_nonempty
    rcases h_nonempty with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    rw [zero_mul]
    unfold additive_valuation
    exact Finset.sum_nonneg (fun x _ => h_nonneg i x)
