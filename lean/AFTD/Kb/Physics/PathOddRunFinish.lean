import AFTD.Prelude

/-!
# pathOddRunFinish

Topic: quantum_mechanics   Node: be7f3b17a647

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

Count odd true runs while retaining a pending run parity.
-/

open scoped BigOperators in
def pathOddRunFinish (prev : Bool) : List Bool → ℕ
  | [] => if prev then 1 else 0
  | b :: bs => (if prev && !b then 1 else 0) + pathOddRunFinish (b && !prev) bs
