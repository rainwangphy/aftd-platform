import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectOneDenseCoreGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectOneDenseCoreColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfDefectOne
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_defect_one_dense_core_witness

Topic: equilibria   Node: 4e222f20e8a6

Provenance: helper lemma. Explicit dense-core example investigated in experiment 16301.

A 12-vertex graph of minimum degree nine has a six-clique, a 1-defective 3-coloring, and a strong 3-color equilibrium.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
instance : DecidableRel maxcut_defect_one_dense_core_graph.Adj := by
  unfold maxcut_defect_one_dense_core_graph
  infer_instance

theorem maxcut_defect_one_dense_core_witness :
    (∀ v : Fin 12, (Finset.univ.filter fun w => maxcut_defect_one_dense_core_graph.Adj v w ∧
      maxcut_defect_one_dense_core_coloring w = maxcut_defect_one_dense_core_coloring v).card ≤ 1) ∧
    (∀ v : Fin 12, 9 ≤ maxcut_defect_one_dense_core_graph.degree v) ∧
    (∀ u ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 12)),
      ∀ v ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 12)),
      u ≠ v → maxcut_defect_one_dense_core_graph.Adj u v) ∧
    ∃ σ : Fin 12 → Fin 3, is_maxcut_strong_equilibrium maxcut_defect_one_dense_core_graph σ := by
  have h :
      (∀ v : Fin 12, (Finset.univ.filter fun w => maxcut_defect_one_dense_core_graph.Adj v w ∧
        maxcut_defect_one_dense_core_coloring w = maxcut_defect_one_dense_core_coloring v).card ≤ 1) ∧
      (∀ v : Fin 12, 9 ≤ maxcut_defect_one_dense_core_graph.degree v) ∧
      (∀ u ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 12)),
        ∀ v ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 12)),
        u ≠ v → maxcut_defect_one_dense_core_graph.Adj u v) := by decide
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  exact (maxcut_strong_equilibrium_of_defect_one maxcut_defect_one_dense_core_graph
    ⟨maxcut_defect_one_dense_core_coloring, h.1⟩).imp (fun _ h => h.1)
