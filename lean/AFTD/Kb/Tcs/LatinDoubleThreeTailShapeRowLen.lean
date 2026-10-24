import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape

/-!
# latin_double_three_tail_shape_rowLen

Topic: combinatorics   Node: ce4f6be46189

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The row-length sanity formula for the staircase with two bottom rows of length three.
-/

theorem latin_double_three_tail_shape_rowLen (k i : ℕ) :
    (latin_double_three_tail_shape k).rowLen i =
      if i < k - 1 then max 3 (k - i) else 0 := by
  apply le_antisymm
  · by_contra h
    have hh : (i, if i < k - 1 then max 3 (k - i) else 0) ∈
        latin_double_three_tail_shape k := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [mem_latin_double_three_tail_shape] at hh
    split_ifs at hh <;> omega
  · by_contra h
    have hh : (i, (latin_double_three_tail_shape k).rowLen i) ∉
        latin_double_three_tail_shape k := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact lt_irrefl _
    rw [mem_latin_double_three_tail_shape] at hh
    split_ifs at h <;> omega
