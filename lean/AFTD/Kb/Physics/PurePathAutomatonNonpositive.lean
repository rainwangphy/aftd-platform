import AFTD.Prelude
import AFTD.Kb.Physics.PathCertRunBound
import AFTD.Kb.Physics.PathCertReachable
import AFTD.Kb.Physics.PathCertPotential
import AFTD.Kb.Physics.PathCertRun

/-!
# pure_path_automaton_nonpositive

Topic: quantum_mechanics   Node: af3c3d50880b

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

For every four-color word, the signed sum of seven greedy path-edge matching counts is nonpositive.
-/

open scoped BigOperators in
theorem pure_path_automaton_nonpositive (a : Fin 4) (xs : List (Fin 4)) :
    (pathCertRun a 0 xs).2.2 ≤ 0 := by
  have hr : pathCertReachable a 0 := by fin_cases a <;> decide
  have h := pathCertRunBound xs a 0 hr
  have hp : pathCertPotential (pathCertRun a 0 xs).2.1 ≤ 0 := by
    unfold pathCertPotential
    split_ifs <;> omega
  have h0 : pathCertPotential 0 = 0 := by decide
  omega
