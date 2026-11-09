import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutNashPivotObstructionGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutNashPivotObstructionStart
import AFTD.Kb.GameTheoryEconomics.MaxcutNashPivotObstructionFinish
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_nash_extension_with_profitable_pivot_coalition

Topic: equilibria   Node: ab271cf96b8a

Provenance: helper lemma. Atlas enumeration in experiment 16715; graph colorings and numerical utility values are printed there.

A best-responding one-conflict vertex can extend a strong deletion equilibrium to a Nash profile that is not strongly stable. A two-vertex deviation has a neutral deletion pivot and a strictly improving partner.
-/

instance : DecidableRel maxcut_nash_pivot_obstruction_graph.Adj := by
  unfold maxcut_nash_pivot_obstruction_graph
  infer_instance

theorem maxcut_nash_extension_with_profitable_pivot_coalition :
    is_maxcut_strong_equilibrium (maxcut_nash_pivot_obstruction_graph.induce (↑(Finset.univ.erase (1 : Fin 6)) : Set (Fin 6)))
      (fun x : (↑(Finset.univ.erase (1 : Fin 6)) : Set (Fin 6)) => maxcut_nash_pivot_obstruction_start x.1) ∧
    (Finset.univ.filter fun w => maxcut_nash_pivot_obstruction_graph.Adj (1 : Fin 6) w ∧ maxcut_nash_pivot_obstruction_start w = maxcut_nash_pivot_obstruction_start 1) = {4} ∧
    (∀ x : Fin 6, ∀ c : Fin 3, ¬ is_maxcut_strong_deviation maxcut_nash_pivot_obstruction_graph maxcut_nash_pivot_obstruction_start {x} (Function.update maxcut_nash_pivot_obstruction_start x c)) ∧
    (∀ c : Fin 3, c ≠ maxcut_nash_pivot_obstruction_start 4 →
      ((Finset.univ.erase (1 : Fin 6)).filter fun w => maxcut_nash_pivot_obstruction_graph.Adj 4 w ∧ maxcut_nash_pivot_obstruction_start w = maxcut_nash_pivot_obstruction_start 4).card <
      ((Finset.univ.erase (1 : Fin 6)).filter fun w => maxcut_nash_pivot_obstruction_graph.Adj 4 w ∧ maxcut_nash_pivot_obstruction_start w = c).card) ∧
    is_maxcut_strong_deviation maxcut_nash_pivot_obstruction_graph maxcut_nash_pivot_obstruction_start ({4, 5} : Finset (Fin 6)) maxcut_nash_pivot_obstruction_finish := by
  refine ⟨by dsimp [is_maxcut_strong_equilibrium, is_maxcut_strong_deviation]; decide,
          by decide,
          by dsimp [is_maxcut_strong_deviation]; decide,
          by decide,
          by dsimp [is_maxcut_strong_deviation]; decide⟩
