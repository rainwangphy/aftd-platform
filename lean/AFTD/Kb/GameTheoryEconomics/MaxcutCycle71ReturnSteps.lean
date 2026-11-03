import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnVertex
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ReturnStages
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_cycle71_return_steps

Topic: equilibria   Node: 99ed0cbdd1f4

Provenance: helper lemma. The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

Every one of the 32 successive restoration moves, including the wraparound, is a profitable deviation by the displayed single vertex and changes no other vertex.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

theorem maxcut_cycle71_return_steps : ∀ i : Fin 32,
    let a : Fin 33 := ⟨i.val + 1, by omega⟩
    let b : Fin 33 := ⟨(i.val + 2) % 33, Nat.mod_lt _ (by decide)⟩
    @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph
      (by intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) 3
      (maxcut_cycle71_return_stages a) {maxcut_cycle71_return_vertex i} (maxcut_cycle71_return_stages b) ∧
    Finset.univ.filter (fun v : Fin 71 => maxcut_cycle71_return_stages b v ≠ maxcut_cycle71_return_stages a v) = {maxcut_cycle71_return_vertex i} := by
  intro i
  fin_cases i <;> unfold is_maxcut_strong_deviation maxcut_utility <;> decide +kernel
