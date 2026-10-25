import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectMul
import AFTD.Kb.Tcs.MondrianRectMulCells
import AFTD.Kb.Tcs.MondrianRectMulDimensions
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_mul

Topic: combinatorics   Node: 73f8152bc745

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Multiplying all rectangle coordinates by a positive integer a sends an admissible c-square partition to an admissible a times c square partition.
-/

theorem mondrian_partition_mul (a c : ℕ) (ha : 0 < a)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition c P) :
    mondrian_is_partition (a * c) (P.map (mondrian_rect_mul a)) := by
  refine ⟨by simpa only [List.length_map] using hp.1, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hx, hy⟩ := hp.2.1 s hs
    exact ⟨Nat.mul_lt_mul_of_pos_left hx ha, Nat.mul_lt_mul_of_pos_left hy ha⟩
  · rw [List.pairwise_map]
    apply hp.2.2.1.imp
    intro r s hrs
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro ⟨i, j⟩ hi hj
      exact Finset.disjoint_left.mp hrs.1
        ((mondrian_rect_mul_cells a ha r i j).mp hi)
        ((mondrian_rect_mul_cells a ha s i j).mp hj)
    · intro hcong
      apply hrs.2
      obtain ⟨hrw, hrh⟩ := mondrian_rect_mul_dimensions a r
      obtain ⟨hsw, hsh⟩ := mondrian_rect_mul_dimensions a s
      rcases hcong with ⟨hw, hh⟩ | ⟨hw, hh⟩
      · left
        constructor
        · apply Nat.eq_of_mul_eq_mul_left ha
          simpa only [hrw, hsw] using hw
        · apply Nat.eq_of_mul_eq_mul_left ha
          simpa only [hrh, hsh] using hh
      · right
        constructor
        · apply Nat.eq_of_mul_eq_mul_left ha
          simpa only [hrw, hsh] using hw
        · apply Nat.eq_of_mul_eq_mul_left ha
          simpa only [hrh, hsw] using hh
  · ext ⟨i, j⟩
    constructor
    · intro hi
      obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      have hi' := (mondrian_rect_mul_cells a ha s i j).mp hi
      have hu : (i / a, j / a) ∈ P.toFinset.biUnion mondrian_rect_cells :=
        Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hs, hi'⟩
      rw [hp.2.2.2] at hu
      simpa only [Finset.mem_product, Finset.mem_range,
        Nat.div_lt_iff_lt_mul ha, Nat.mul_comm] using hu
    · intro hi
      have hu : (i / a, j / a) ∈ Finset.range c ×ˢ Finset.range c := by
        simpa only [Finset.mem_product, Finset.mem_range,
          Nat.div_lt_iff_lt_mul ha, Nat.mul_comm] using hi
      rw [← hp.2.2.2] at hu
      obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hu
      apply Finset.mem_biUnion.mpr
      refine ⟨mondrian_rect_mul a r, ?_, (mondrian_rect_mul_cells a ha r i j).mpr hm⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩)
