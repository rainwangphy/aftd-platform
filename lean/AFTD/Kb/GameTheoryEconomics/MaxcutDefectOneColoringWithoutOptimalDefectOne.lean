import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectOneNonoptimalGraph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_defect_one_coloring_without_optimal_defect_one

Topic: equilibria   Node: c13d96b7e3f0

Provenance: helper lemma. Independent finite enumeration experiments 16395 and 16399.

The eight-vertex graph has a defect-one three-coloring but no optimal three-coloring has defect one.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
instance : DecidableRel maxcut_defect_one_nonoptimal_graph.Adj := by
  unfold maxcut_defect_one_nonoptimal_graph
  infer_instance

private def in582_defective : Fin 8 → Fin 3 := ![0,1,0,1,0,0,2,1]
private def in582_better : Fin 8 → Fin 3 := ![0,1,0,1,2,2,0,2]

private theorem in582_defect_one_strictly_below_better :
    ∀ σ : Fin 8 → Fin 3,
      (∀ v : Fin 8, (Finset.univ.filter fun w => maxcut_defect_one_nonoptimal_graph.Adj v w ∧ σ w = σ v).card ≤ 1) →
      maxcut_welfare maxcut_defect_one_nonoptimal_graph σ < maxcut_welfare maxcut_defect_one_nonoptimal_graph in582_better := by
  decide

theorem maxcut_defect_one_coloring_without_optimal_defect_one :
    (∃ σ : Fin 8 → Fin 3, ∀ v : Fin 8,
      (Finset.univ.filter fun w => maxcut_defect_one_nonoptimal_graph.Adj v w ∧ σ w = σ v).card ≤ 1) ∧
    ∀ σ : Fin 8 → Fin 3,
      (∀ v : Fin 8, (Finset.univ.filter fun w => maxcut_defect_one_nonoptimal_graph.Adj v w ∧ σ w = σ v).card ≤ 1) →
      ¬ is_maxcut_optimal maxcut_defect_one_nonoptimal_graph σ := by
  constructor
  · refine ⟨in582_defective, ?_⟩
    decide
  · intro σ hdef hopt
    exact (Nat.not_lt_of_ge (hopt in582_better)) (in582_defect_one_strictly_below_better σ hdef)
