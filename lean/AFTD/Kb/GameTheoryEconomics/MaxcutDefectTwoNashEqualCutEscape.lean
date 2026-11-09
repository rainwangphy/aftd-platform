import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoEscapeGraph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_defect_two_nash_equal_cut_escape

Topic: equilibria   Node: 093ce8ea9322

Provenance: helper lemma. Independent direct verification in experiments 16323–16324.

A defect-two Nash coloring can have a strong deviation of equal welfare to a coloring of defect at least four.
-/

instance maxcut_defect_two_nash_equal_cut_escape_adj :
    DecidableRel maxcut_defect_two_escape_graph.Adj := by
  dsimp [maxcut_defect_two_escape_graph, SimpleGraph.fromRel]
  infer_instance

instance maxcut_defect_two_nash_equal_cut_escape_dev
    {k : ℕ} (σ : Fin 15 → Fin k) (S : Finset (Fin 15)) (τ : Fin 15 → Fin k) :
    Decidable (is_maxcut_strong_deviation maxcut_defect_two_escape_graph σ S τ) := by
  dsimp [is_maxcut_strong_deviation]
  infer_instance

theorem maxcut_defect_two_nash_equal_cut_escape
    [DecidableRel maxcut_defect_two_escape_graph.Adj] :
    (∀ v : Fin 15, (Finset.univ.filter fun w => maxcut_defect_two_escape_graph.Adj v w ∧
      (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3) w = (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3) v).card ≤ 2) ∧
    (∀ v : Fin 15, ∀ c : Fin 3, ¬ is_maxcut_strong_deviation maxcut_defect_two_escape_graph
      (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3) {v} (Function.update (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3) v c)) ∧
    is_maxcut_strong_deviation maxcut_defect_two_escape_graph (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3)
      (Finset.univ.filter fun v : Fin 15 => v.val < 12) (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2] : Fin 15 → Fin 3) ∧
    maxcut_welfare maxcut_defect_two_escape_graph (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2] : Fin 15 → Fin 3) = maxcut_welfare maxcut_defect_two_escape_graph (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2] : Fin 15 → Fin 3) ∧
    ∃ v : Fin 15, 4 ≤ (Finset.univ.filter fun w => maxcut_defect_two_escape_graph.Adj v w ∧
      (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2] : Fin 15 → Fin 3) w = (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2] : Fin 15 → Fin 3) v).card := by
  rename_i inst
  have : inst = maxcut_defect_two_nash_equal_cut_escape_adj := Subsingleton.elim _ _
  subst this
  decide
