import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOrPower
import AFTD.Kb.Tcs.ShannonOrCapacityCategoricalProdLeMin
import AFTD.Kb.Tcs.SimpleGraphCategoricalProd
import AFTD.Kb.Tcs.ShannonOrCapacity

/-!
# shannon_or_capacity_categorical_prod_of_min_eq_one

Topic: information   Node: 06337ee94d00

Provenance: formalization of a published result. Source: arXiv:2610.41977 Sec. 6

For any finite nonempty simple graphs G and H, if the minimum of their Shannon OR-capacities is 1, then the Shannon OR-capacity of their categorical product G × H is 1.
-/

private lemma shannon_or_capacity_categorical_prod_of_min_eq_one_cliqueNum_pos
    {α : Type*} [Fintype α] [Nonempty α] (P : SimpleGraph α) : 1 ≤ P.cliqueNum := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hcl : P.IsClique (↑({a} : Finset α)) := by
    simpa using SimpleGraph.isClique_singleton (G := P) a
  have hcard := SimpleGraph.IsClique.card_le_cliqueNum (G := P) (t := ({a} : Finset α)) (tc := hcl)
  simpa using hcard

/-- Hedetniemi's identity for Shannon OR-capacity holds when the smaller factor capacity is one. -/
theorem shannon_or_capacity_categorical_prod_of_min_eq_one {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W] (G : SimpleGraph V) (H : SimpleGraph W) (h : min (shannon_or_capacity G) (shannon_or_capacity H) = 1) : shannon_or_capacity (simple_graph_categorical_prod G H) = 1 := by
  have hle : shannon_or_capacity (simple_graph_categorical_prod G H) ≤ 1 := by
    simpa [h] using shannon_or_capacity_categorical_prod_le_min G H
  refine le_antisymm hle ?_
  have hbdd := shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range
    (simple_graph_categorical_prod G H)
  have hterm : (1:ℝ) ≤ ⨆ (_ : 1 ≤ (1:ℕ)),
      ((simple_graph_or_power (simple_graph_categorical_prod G H) 1).cliqueNum : ℝ) ^ ((1:ℝ)/↑(1:ℕ)) := by
    rw [ciSup_pos (le_refl 1)]
    have hcl' : 1 ≤ (simple_graph_or_power (simple_graph_categorical_prod G H) 1).cliqueNum :=
      shannon_or_capacity_categorical_prod_of_min_eq_one_cliqueNum_pos _
    have hcl : (1:ℝ) ≤ ((simple_graph_or_power (simple_graph_categorical_prod G H) 1).cliqueNum : ℝ) := by
      exact_mod_cast hcl'
    rw [show (1:ℝ)/↑(1:ℕ) = 1 by norm_num, Real.rpow_one]
    exact hcl
  exact le_trans hterm (le_ciSup hbdd 1)
