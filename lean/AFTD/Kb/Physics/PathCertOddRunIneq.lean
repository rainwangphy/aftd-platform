import AFTD.Prelude
import AFTD.Kb.Physics.PathCertWord
import AFTD.Kb.Physics.PathCertSign
import AFTD.Kb.Physics.PathCertRunEqGreedy
import AFTD.Kb.Physics.PurePathAutomatonNonpositive
import AFTD.Kb.Physics.PathCertWordCountCancel
import AFTD.Kb.Physics.PathGreedyRunEqCountAndOdd
import AFTD.Kb.Physics.OddRunCount
import AFTD.Kb.Physics.PathGreedyRun
import AFTD.Kb.Physics.PathCertRun

/-!
# pathCertOddRunIneq

Topic: quantum_mechanics   Node: 99723cb851a0

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

For any four-color path word, the signed sum of odd crossing-run counts for the seven masks is nonpositive.
-/

open scoped BigOperators in
theorem pathCertOddRunIneq (a : Fin 4) (xs : List (Fin 4)) :
    (∑ j : Fin 7, pathCertSign j * (odd_run_count (pathCertWord a xs j) : ℤ)) ≤ 0 := by
  have hbound : (∑ j : Fin 7, pathCertSign j * (pathGreedyRun false (pathCertWord a xs j) : ℤ)) ≤ 0 := by
    simpa [pathCertRun_eq_greedy] using pure_path_automaton_nonpositive a xs
  have hcount := pathCertWordCountCancel a xs
  have hid : (2 : ℤ) * (∑ j : Fin 7, pathCertSign j * (pathGreedyRun false (pathCertWord a xs j) : ℤ)) =
      (∑ j : Fin 7, pathCertSign j * ((pathCertWord a xs j).countP id : ℤ)) +
      (∑ j : Fin 7, pathCertSign j * (odd_run_count (pathCertWord a xs j) : ℤ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have h := pathGreedyRun_eq_count_and_odd (pathCertWord a xs j)
    have hz : (2 : ℤ) * (pathGreedyRun false (pathCertWord a xs j) : ℤ) =
      ((pathCertWord a xs j).countP id : ℤ) + (odd_run_count (pathCertWord a xs j) : ℤ) := by exact_mod_cast h
    calc
      _ = pathCertSign j * (2 * (pathGreedyRun false (pathCertWord a xs j) : ℤ)) := by ring
      _ = pathCertSign j * (((pathCertWord a xs j).countP id : ℤ) + (odd_run_count (pathCertWord a xs j) : ℤ)) := by rw [hz]
      _ = _ := by ring
  omega
