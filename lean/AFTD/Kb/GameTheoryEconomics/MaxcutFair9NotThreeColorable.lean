import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph

/-!
# maxcut_fair9_not_three_colorable

Topic: equilibria   Node: 3935c33fff63

Provenance: helper lemma. Experiment 12998 identifies a four-vertex clique in the finite fairness obstruction related to OP-85.

The specified nine-vertex fairness-obstruction graph does not admit a proper coloring with three colors.
-/

private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance

lemma maxcut_fair9_not_three_colorable_clique_4 (a b c d : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> contradiction

theorem maxcut_fair9_not_three_colorable :
    ¬ ∃ σ : Fin 9 → Fin 3, ∀ v w : Fin 9, maxcut_fair9_graph.Adj v w → σ v ≠ σ w := by
  intro ⟨σ, hσ⟩
  exact maxcut_fair9_not_three_colorable_clique_4 (σ 3) (σ 4) (σ 5) (σ 8)
    (hσ 3 4 (by decide)) (hσ 3 5 (by decide)) (hσ 3 8 (by decide))
    (hσ 4 5 (by decide)) (hσ 4 8 (by decide)) (hσ 5 8 (by decide))
