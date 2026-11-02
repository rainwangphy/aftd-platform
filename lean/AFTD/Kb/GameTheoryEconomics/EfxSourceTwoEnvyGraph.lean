import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxSourceTwoValues
import AFTD.Kb.GameTheoryEconomics.EfxSourceTwoStart
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_source_two_envy_graph

Topic: fair_division   Node: 4acc2b553452

Provenance: helper lemma. Nine-good isolated-source completion obstruction; experiments 11561–11562.

The starting envy graph has exactly one edge, from agent 0 to agent 2, and thus three sources.
-/

theorem efx_source_two_envy_graph (i j : Fin 4) (hij : i ≠ j) :
  (efx_partial_nat_utility efx_source_two_values efx_source_two_start i <
    ∑ g : Fin 9, if efx_source_two_start g = j.castSucc then efx_source_two_values i g else 0) ↔
  (i = 0 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [efx_partial_nat_utility, efx_source_two_values, efx_source_two_start,
      Fin.sum_univ_succ]
