import AFTD.Prelude
import AFTD.Kb.Physics.PathCertMask

/-!
# pathCertWord

Topic: quantum_mechanics   Node: 9a317120eaea

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

The sequence of cut-crossing flags for one party-union mask along a colored vertex word.
-/

open scoped BigOperators in
def pathCertWord (a : Fin 4) : List (Fin 4) → Fin 7 → List Bool
  | [], _ => []
  | b :: bs, j => (Nat.testBit (pathCertMask j) a.val != Nat.testBit (pathCertMask j) b.val) :: pathCertWord b bs j
