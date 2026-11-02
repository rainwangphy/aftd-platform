import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle46Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle46Coloring
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle46Deviations
import AFTD.Kb.GameTheoryEconomics.MaxcutFiveCycleRepeats
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_unweighted_strong_deviation_cycle_exists

Topic: equilibria   Node: 22c4e05c8941

Provenance: original. Related work: arXiv:1810.09278, Proposition 2 gives a cycle for a weighted game; Section 7 discusses strong potential in unweighted games. Related existence question: arXiv:2610.04948, Section 4.

There is an unweighted simple graph on 46 vertices and an infinite sequence of three-color profiles that returns to its starting profile after five steps, such that every consecutive pair is a profitable deviation by exactly the players who change colors.
-/

private instance cycle46_decidable : DecidableRel maxcut_cycle46_graph.Adj := by
  intro u v
  unfold maxcut_cycle46_graph SimpleGraph.fromRel
  infer_instance

theorem maxcut_unweighted_strong_deviation_cycle_exists :
    ∃ (G : SimpleGraph (Fin 46)) (d : DecidableRel G.Adj) (f : ℕ → Fin 46 → Fin 3),
      f 5 = f 0 ∧ ∀ n, @is_maxcut_strong_deviation _ _ G d 3 (f n)
        (Finset.univ.filter fun v => f (n + 1) v ≠ f n v) (f (n + 1)) := by
  obtain ⟨f, hperiod, hsteps⟩ := maxcut_five_cycle_repeats maxcut_cycle46_graph maxcut_cycle46_coloring maxcut_cycle46_deviations
  exact ⟨maxcut_cycle46_graph, cycle46_decidable, f, hperiod, hsteps⟩
