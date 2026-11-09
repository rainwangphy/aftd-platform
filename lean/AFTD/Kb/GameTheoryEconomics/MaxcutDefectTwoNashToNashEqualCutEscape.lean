import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoNashEscapeGraph
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_defect_two_nash_to_nash_equal_cut_escape

Topic: equilibria   Node: 8e7a7959240b

Provenance: helper lemma. Independent exact checks 16337–16338.

A defect-two Nash coloring can strongly deviate at equal welfare to another Nash coloring of defect at least four.
-/

@[instance_reducible] def maxcut_defect_two_nash_to_nash_equal_cut_escape_adj :
    DecidableRel maxcut_defect_two_nash_escape_graph.Adj := by
  dsimp [maxcut_defect_two_nash_escape_graph]
  infer_instance

instance maxcut_defect_two_nash_to_nash_equal_cut_escape_dev
    {k : ℕ} (σ : Fin 27 → Fin k) (S : Finset (Fin 27)) (τ : Fin 27 → Fin k) :
    Decidable (@is_maxcut_strong_deviation (Fin 27) _ maxcut_defect_two_nash_escape_graph
      maxcut_defect_two_nash_to_nash_equal_cut_escape_adj k σ S τ) := by
  dsimp [is_maxcut_strong_deviation]
  infer_instance

theorem maxcut_defect_two_nash_to_nash_equal_cut_escape
    [DecidableRel maxcut_defect_two_nash_escape_graph.Adj] :
    (∀ v : Fin 27, (Finset.univ.filter fun w => maxcut_defect_two_nash_escape_graph.Adj v w ∧
      (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) w = (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) v).card ≤ 2) ∧
    (∀ v : Fin 27, ∀ d : Fin 3, ¬ is_maxcut_strong_deviation maxcut_defect_two_nash_escape_graph (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) {v} (Function.update (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) v d)) ∧ (∀ v : Fin 27, ∀ d : Fin 3, ¬ is_maxcut_strong_deviation maxcut_defect_two_nash_escape_graph (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) {v} (Function.update (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) v d)) ∧
    is_maxcut_strong_deviation maxcut_defect_two_nash_escape_graph (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3)
      (Finset.univ.filter fun v : Fin 27 => v.val < 12) (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) ∧
    maxcut_welfare maxcut_defect_two_nash_escape_graph (![0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) =
      maxcut_welfare maxcut_defect_two_nash_escape_graph (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) ∧
    ∃ v : Fin 27, 4 ≤ (Finset.univ.filter fun w => maxcut_defect_two_nash_escape_graph.Adj v w ∧
      (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) w = (![1,2,1,2,2,0,2,0,0,1,0,1,0,1,2,1,1,2,2,0,0,2,2,0,0,1,1] : Fin 27 → Fin 3) v).card := by
  rename_i inst
  have : inst = maxcut_defect_two_nash_to_nash_equal_cut_escape_adj := Subsingleton.elim _ _
  subst this
  decide
