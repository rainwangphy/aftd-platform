import AFTD.Prelude
import AFTD.Kb.Physics.PathCertNext
import AFTD.Kb.Physics.PathCertDelta

/-!
# pathCertRun

Topic: quantum_mechanics   Node: e418fc70dfc0

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Run the seven simultaneous greedy matching counters on a colored path suffix.
-/

open scoped BigOperators in
def pathCertRun (a : Fin 4) (s : Fin 128) : List (Fin 4) → Fin 4 × Fin 128 × ℤ
  | [] => (a,s,0)
  | b :: bs =>
    let (last, bits, val) := pathCertRun b (pathCertNext a b s) bs
    (last, bits, pathCertDelta a b s + val)
