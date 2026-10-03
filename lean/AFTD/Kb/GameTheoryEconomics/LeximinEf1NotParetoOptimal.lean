import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsLeximinEf1
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimalGoods
import AFTD.Kb.GameTheoryEconomics.LxvValues
import AFTD.Kb.GameTheoryEconomics.LxvVal
import AFTD.Kb.GameTheoryEconomics.LxvOpt
import AFTD.Kb.GameTheoryEconomics.LxvDom
import AFTD.Kb.GameTheoryEconomics.LxvInstance
import AFTD.Kb.GameTheoryEconomics.LxvCheckSpec
import AFTD.Kb.GameTheoryEconomics.LxvGoodsUtility
import AFTD.Kb.GameTheoryEconomics.LxvIsEf1Iff
import AFTD.Kb.GameTheoryEconomics.LxvLeximinLtIff

/-!
# leximin_ef1_not_pareto_optimal

Topic: fair_division   Node: 9ed374916b9a

Choosing the leximin-optimal allocation among EF1 allocations does not guarantee Pareto optimality, even for normalised additive valuations: with 4 agents and 6 goods, a leximin-optimal EF1 allocation exists and every one is Pareto-dominated.
-/

/-- **Leximin among EF1 allocations is not Pareto optimal** (conjectured by Caragiannis, Kurokawa, Moulin, Procaccia, Shah and Wang, The Unreasonable Fairness of Maximum Nash Welfare, App. B). Four agents, six goods, additive values normalised to sum to 1: there is a leximin-optimal EF1 allocation, and every leximin-optimal EF1 allocation is Pareto-dominated. -/
theorem leximin_ef1_not_pareto_optimal :
    ∃ u : Fin 4 → Fin 6 → ℝ, (∀ i g, 0 ≤ u i g) ∧ (∀ i, ∑ g, u i g = 1) ∧
      (∃ σ, is_leximin_ef1 u σ) ∧ ∀ σ, is_leximin_ef1 u σ → ¬ is_pareto_optimal_goods u σ := by
  obtain ⟨hopt, hall⟩ := lxv_check_spec
  have hlex : is_leximin_ef1 lxv_instance lxv_opt := by
    refine ⟨(lxv_is_ef1_iff _).2 hopt, fun τ hτ => ?_⟩
    rw [lxv_leximin_lt_iff]
    exact (hall τ ((lxv_is_ef1_iff τ).1 hτ)).1
  refine ⟨lxv_instance, fun i g => by unfold lxv_instance; positivity, fun i => ?_, ⟨_, hlex⟩, ?_⟩
  · simp only [lxv_instance, ← Finset.sum_div, Fin.sum_univ_six]
    fin_cases i <;> simp [lxv_values] <;> norm_num
  · intro σ hσ
    have hσo : σ = lxv_opt := by
      rcases (hall σ ((lxv_is_ef1_iff σ).1 hσ.1)).2 with h | h
      · exact absurd ((lxv_leximin_lt_iff _ _).2 h) (hσ.2 _ hlex.1)
      · exact h
    subst hσo
    intro hpo
    apply hpo
    have hN : (∀ i, lxv_val lxv_opt i i ≤ lxv_val lxv_dom i i) ∧
        lxv_val lxv_opt 2 2 < lxv_val lxv_dom 2 2 := by decide
    refine ⟨lxv_dom, fun i => ?_, 2, ?_⟩
    · rw [lxv_goods_utility, lxv_goods_utility]
      exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hN.1 i)) (by norm_num)
    · rw [lxv_goods_utility, lxv_goods_utility]
      exact div_lt_div_of_pos_right (Nat.cast_lt.2 hN.2) (by norm_num)
