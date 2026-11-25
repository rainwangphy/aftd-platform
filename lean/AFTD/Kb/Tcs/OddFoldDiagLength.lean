import AFTD.Prelude
import AFTD.Kb.Tcs.OddFoldDiag

/-!
# oddFoldDiag_length

Topic: combinatorics   Node: 633092b179bd

Provenance: helper lemma. arXiv:2611.28952, Section 1.1, (2)

The diagonal of the odd fold of a list d has length 2 * |d| + 1.
-/

/-- Length of the diagonal of an odd fold. -/
theorem oddFoldDiag_length {R : Type*} [Zero R] (d : List R) :
    (oddFoldDiag d).length = 2 * d.length + 1 := by
  simp [oddFoldDiag]
  omega
