import AFTD.Prelude
import AFTD.Kb.Physics.PathCertTake

/-!
# pathCertNext

Topic: quantum_mechanics   Node: f697cb03fd10

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The seven greedy-matching flags after appending a colored vertex.
-/

open scoped BigOperators in
def pathCertNext (a b : Fin 4) (s : Fin 128) : Fin 128 :=
  ⟨(∑ j : Fin 7, if pathCertTake a b s j then 2 ^ j.val else 0) % 128, Nat.mod_lt _ (by decide)⟩
