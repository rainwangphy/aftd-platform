import AFTD.Prelude
import AFTD.Kb.Physics.PathCertRun
import AFTD.Kb.Physics.PathCertStep
import AFTD.Kb.Physics.PathCertPotential
import AFTD.Kb.Physics.PathCertDelta
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.PathCertReachable
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.PathCertNext

/-!
# pathCertRunBound

Topic: quantum_mechanics   Node: 766bf138561c

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The accumulated signed greedy count is bounded by the finite-state potential.
-/

open scoped BigOperators in
theorem pathCertRunBound (xs : List (Fin 4)) (a : Fin 4) (s : Fin 128)
    (h : pathCertReachable a s) :
    pathCertPotential s + (pathCertRun a s xs).2.2 ≤ pathCertPotential (pathCertRun a s xs).2.1 := by
  set_option maxHeartbeats 5000000 in
    induction xs generalizing a s with
    | nil => simp [pathCertRun]
    | cons b bs ih =>
      have hstep := pathCertStep a b s h
      have hrest := ih b (pathCertNext a b s) hstep.1
      change pathCertPotential s + (pathCertDelta a b s + (pathCertRun b (pathCertNext a b s) bs).2.2) ≤ pathCertPotential (pathCertRun b (pathCertNext a b s) bs).2.1
      calc
        _ = (pathCertPotential s + pathCertDelta a b s) + (pathCertRun b (pathCertNext a b s) bs).2.2 := by ring
        _ ≤ pathCertPotential (pathCertNext a b s) + (pathCertRun b (pathCertNext a b s) bs).2.2 := by
          have hh := hstep.2
          omega
        _ ≤ _ := hrest
