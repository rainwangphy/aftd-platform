import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianDefectZeroOfEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionMul
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectMul
import AFTD.Kb.Tcs.MondrianRectMulArea

/-!
# mondrian_perfect_partition_mul

Topic: combinatorics   Node: 1f5b712233b4

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Multiplying all coordinates by a positive integer preserves perfect admissible partitions.
-/

theorem mondrian_perfect_partition_mul (a c : ℕ) (ha : 0 < a)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition c P)
    (hz : mondrian_defect P = 0) :
    mondrian_is_partition (a * c) (P.map (mondrian_rect_mul a)) ∧
      mondrian_defect (P.map (mondrian_rect_mul a)) = 0 := by
  refine ⟨mondrian_partition_mul a c ha P hp, ?_⟩
  cases P with
  | nil => simp [mondrian_defect]
  | cons r P =>
    apply mondrian_defect_zero_of_equal _ (mondrian_rect_area (mondrian_rect_mul a r))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    rw [mondrian_rect_mul_area, mondrian_rect_mul_area]
    rw [mondrian_defect_zero_equal (r :: P) hz t r ht (by simp)]
