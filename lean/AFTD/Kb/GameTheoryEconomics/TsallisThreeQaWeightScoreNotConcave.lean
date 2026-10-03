import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsQaPool
import AFTD.Kb.GameTheoryEconomics.ProperScoreOfExposure
import AFTD.Kb.GameTheoryEconomics.QaCounterexampleForecasts
import AFTD.Kb.GameTheoryEconomics.QaPoolTsallisThreeOfKkt
import AFTD.Kb.GameTheoryEconomics.TsallisExpectedReward
import AFTD.Kb.GameTheoryEconomics.TsallisExposure

/-!
# tsallis_three_qa_weight_score_not_concave

Topic: mechanism_design   Node: 33664e168092

Without convex exposure the QA weight-score need not be concave: for the cubic Tsallis rule, forecasts (0,0,1), (1/4,3/4,0), outcome 1, weights v = (3/10,7/10), w = (0,1) and t = 2/3, the score of the pool at t v + (1-t) w is strictly less than t times the score at v plus (1-t) times the score at w.
-/

/-- arXiv:2102.07081 (Sec. 7) asks whether Theorem 5.1 (the weight-score of the QA pool is concave in the weights) holds without convex exposure. It does not: for the cubic Tsallis rule, three outcomes, experts `(0,0,1)` and `(1/4,3/4,0)`, outcome 1 and weights `(0,1)`, `(3/10,7/10)` and their `1/3 : 2/3` mixture `(1/5,4/5)`, the score at the mixture is strictly below the mixture of the scores. -/
theorem tsallis_three_qa_weight_score_not_concave :
    ∃ (ps : Fin 2 → Fin 3 → ℝ) (v w : Fin 2 → ℝ) (t : ℝ) (xv xw xt : Fin 3 → ℝ) (j : Fin 3),
      (∀ i, ps i ∈ stdSimplex ℝ (Fin 3)) ∧ v ∈ stdSimplex ℝ (Fin 2) ∧
      w ∈ stdSimplex ℝ (Fin 2) ∧ 0 ≤ t ∧ t ≤ 1 ∧
      is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) ps v xv ∧
      is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) ps w xw ∧
      is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) ps (t • v + (1 - t) • w) xt ∧
      proper_score_of_exposure (tsallis_expected_reward 3) (tsallis_exposure 3) xt j <
        t * proper_score_of_exposure (tsallis_expected_reward 3) (tsallis_exposure 3) xv j +
          (1 - t) * proper_score_of_exposure (tsallis_expected_reward 3) (tsallis_exposure 3) xw j := by
  refine ⟨qa_counterexample_forecasts, ![3/10, 7/10], ![0, 1], 2/3, ![0, 35/64, 29/64],
    ![1/4, 3/4, 0], ![0, 5/8, 3/8], 0, ?_, ?_, ?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;>
      exact ⟨fun k => by fin_cases k <;> norm_num [qa_counterexample_forecasts],
        by simp [qa_counterexample_forecasts, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] <;> norm_num⟩
  · exact ⟨fun k => by fin_cases k <;> simp <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
  · exact ⟨fun k => by fin_cases k <;> simp, by simp [Fin.sum_univ_two]⟩
  · refine qa_pool_tsallis_three_of_kkt _ _ (-5817/20480)
      ⟨fun k => by fin_cases k <;> simp <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩ ?_
    intro k
    fin_cases k <;>
      simp [Fin.sum_univ_two, tsallis_exposure, qa_counterexample_forecasts] <;> norm_num
  · refine qa_pool_tsallis_three_of_kkt _ _ 0
      ⟨fun k => by fin_cases k <;> simp <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩ ?_
    intro k
    fin_cases k <;>
      simp [Fin.sum_univ_two, tsallis_exposure, qa_counterexample_forecasts] <;> norm_num
  · refine qa_pool_tsallis_three_of_kkt _ _ (-57/320)
      ⟨fun k => by fin_cases k <;> simp <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩ ?_
    intro k
    fin_cases k <;>
      simp [Fin.sum_univ_two, tsallis_exposure, qa_counterexample_forecasts] <;> norm_num
  · simp [proper_score_of_exposure, tsallis_expected_reward, tsallis_exposure, Fin.sum_univ_three]
    norm_num
