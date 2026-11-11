import AFTD.Prelude
import AFTD.Kb.Physics.PathCertMask

/-!
# pathCertTake

Topic: quantum_mechanics   Node: c510ea915646

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Greedy matching choice for one cut when a path edge is appended.
-/

open scoped BigOperators in
def pathCertTake (a b : Fin 4) (s : Fin 128) (j : Fin 7) : Bool :=
  (Nat.testBit (pathCertMask j) a.val != Nat.testBit (pathCertMask j) b.val) &&
    !(Nat.testBit s.val j.val)
