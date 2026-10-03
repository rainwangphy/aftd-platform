import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.GameTheoryEconomics.LxvVal
import AFTD.Kb.GameTheoryEconomics.LxvInstance
import AFTD.Kb.GameTheoryEconomics.LxvAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.LxvSumBundle

/-!
# lxv_goods_utility

Topic: fair_division   Node: a473fbd675df

The real utility vector of an allocation in the instance is its integer own-bundle values divided by 20.
-/

lemma lxv_goods_utility (a : Fin 6 → Fin 4) :
    goods_utility lxv_instance a = fun i => ((lxv_val a i i : ℕ) : ℝ) / 20 := by
  funext i; simp only [goods_utility, lxv_additive_valuation, lxv_sum_bundle]
