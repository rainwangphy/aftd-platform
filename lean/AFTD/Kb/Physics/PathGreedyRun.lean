import AFTD.Prelude

/-!
# pathGreedyRun

Topic: quantum_mechanics   Node: 450ac206068f

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Greedily count disjoint true edges in a Boolean edge word.
-/

open scoped BigOperators in
def pathGreedyRun (prev : Bool) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b && !prev then 1 else 0) + pathGreedyRun (b && !prev) bs
