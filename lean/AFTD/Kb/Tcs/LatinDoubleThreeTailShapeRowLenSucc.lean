import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen

/-!
# latin_double_three_tail_shape_rowLen_succ

Topic: combinatorics   Node: 33f16a0e8731

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

Deleting the top row of the shape at k+1 leaves the shape at k, with row indices shifted by one.
-/

theorem latin_double_three_tail_shape_rowLen_succ (k i : ℕ) :
    (latin_double_three_tail_shape (k+1)).rowLen (i+1) =
      (latin_double_three_tail_shape k).rowLen i := by
  rw [latin_double_three_tail_shape_rowLen, latin_double_three_tail_shape_rowLen]
  split_ifs <;> omega
