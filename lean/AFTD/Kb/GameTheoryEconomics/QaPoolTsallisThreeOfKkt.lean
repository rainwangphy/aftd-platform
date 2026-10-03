import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsQaPool
import AFTD.Kb.GameTheoryEconomics.QaCounterexampleForecasts
import AFTD.Kb.GameTheoryEconomics.QaPoolTsallisThreeAux
import AFTD.Kb.GameTheoryEconomics.TsallisExpectedReward
import AFTD.Kb.GameTheoryEconomics.TsallisExposure

/-!
# qa_pool_tsallis_three_of_kkt

Topic: mechanism_design   Node: 987a0d40c2c0

For the two counterexample forecasts and any weights, a simplex point meeting the KKT conditions is the cubic Tsallis QA pool.
-/

lemma qa_pool_tsallis_three_of_kkt (w : Fin 2 → ℝ) (x : Fin 3 → ℝ) (lam : ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin 3))
    (hkkt : ∀ k, lam ≤ 3 * x k ^ 2 - ∑ i, w i * tsallis_exposure 3 (qa_counterexample_forecasts i) k ∧
      (0 < x k → 3 * x k ^ 2 - ∑ i, w i * tsallis_exposure 3 (qa_counterexample_forecasts i) k = lam)) :
    is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) qa_counterexample_forecasts w x :=
  ⟨hx, qa_pool_tsallis_three_aux _ x lam hx hkkt⟩
