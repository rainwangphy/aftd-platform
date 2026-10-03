import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costFinTwoCases

/-!
# ef1cost_opt_le

Topic: fair_division   Node: ffbd10db7787

For two agents, giving each item to agent 0 when c_0 <= c_1 and to agent 1 otherwise minimises the item-wise cost sum.
-/

lemma ef1cost_opt_le {m : ℕ} (c : Fin 2 → Fin m → ℝ) (τ : Fin m → Fin 2) :
    ∑ j, c (if c 0 j ≤ c 1 j then 0 else 1) j ≤ ∑ j, c (τ j) j := by
  refine Finset.sum_le_sum (fun j _ => ?_)
  rcases ef1cost_fin_two_cases 0 1 (by decide) (τ j) with h | h <;> rw [h] <;>
    split_ifs with hc
  · exact le_refl _
  · linarith
  · exact hc
  · exact le_refl _
