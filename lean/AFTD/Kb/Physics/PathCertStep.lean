import AFTD.Prelude
import AFTD.Kb.Physics.PathCertNext
import AFTD.Kb.Physics.PathCertDelta
import AFTD.Kb.Physics.PathCertReachable
import AFTD.Kb.Physics.PathCertPotential

/-!
# pathCertStep

Topic: quantum_mechanics   Node: 5cfe151bb30b

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Each reachable transition remains reachable and respects the path certificate potential.
-/

open scoped BigOperators in
theorem pathCertStep (a b : Fin 4) (s : Fin 128) (h : pathCertReachable a s) :
    pathCertReachable b (pathCertNext a b s) ∧
    pathCertPotential s + pathCertDelta a b s ≤ pathCertPotential (pathCertNext a b s) := by
  set_option maxHeartbeats 5000000 in
    set_option maxRecDepth 100000 in
      revert a b s
      decide
