import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianPartitionAreaSum
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_partition_zero_one_impossible

Topic: combinatorics   Node: affd24a68360

Provenance: helper lemma. step towards mondrian_no_perfect_partition

An integer square of side n <= 1 has no admissible Mondrian partition.
-/

/-- An integer square of side n <= 1 has no admissible Mondrian partition. -/
theorem mondrian_partition_zero_one_impossible (n : ℕ) (hn : n ≤ 1) :
    ¬ ∃ P, mondrian_is_partition n P := by
  rintro ⟨P, hP⟩
  have hsum := mondrian_partition_area_sum n P hP
  have hpos : ∀ r ∈ P, 1 ≤ mondrian_rect_area r := by
    intro r hr
    have h := hP.2.1 r hr
    unfold mondrian_rect_area mondrian_rect_width mondrian_rect_height
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hlen : P.length ≤ (P.map mondrian_rect_area).sum := by
    have : (P.map (fun _ => 1)).sum ≤ (P.map mondrian_rect_area).sum :=
      List.sum_le_sum (by
        intro r hr
        exact hpos r hr)
    simpa using this
  have h2 := hP.1
  have hn2 : n ^ 2 ≤ 1 := by
    calc n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hn 2
      _ = 1 := by norm_num
  omega
