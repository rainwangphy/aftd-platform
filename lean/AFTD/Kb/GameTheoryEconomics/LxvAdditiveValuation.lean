import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvValues
import AFTD.Kb.GameTheoryEconomics.LxvInstance
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# lxv_additive_valuation

Topic: fair_division   Node: 3b4a4421a111

In the instance, the additive value of a set is its integer value divided by 20.
-/

lemma lxv_additive_valuation (i : Fin 4) (S : Finset (Fin 6)) :
    additive_valuation (lxv_instance i) S = ((∑ g ∈ S, lxv_values i g : ℕ) : ℝ) / 20 := by
  simp [additive_valuation, lxv_instance, Finset.sum_div]
