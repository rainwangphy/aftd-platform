import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIntervalDiv
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectDivCells
import AFTD.Kb.Tcs.MondrianRectDivDimensions
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_div

Topic: combinatorics   Node: 1b15e23824a9

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

An admissible partition of the a times c square, with every tile side a multiple of positive a, becomes an admissible partition of the c-square after dividing coordinates by a.
-/

theorem mondrian_partition_div (a c : ℕ) (ha : 0 < a)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition (a * c) P)
    (hd : ∀ r ∈ P, a ∣ mondrian_rect_width r ∧ a ∣ mondrian_rect_height r) :
    mondrian_is_partition c (P.map (mondrian_rect_div a)) := by
  have hdim : ∀ r ∈ P,
      a * mondrian_rect_width (mondrian_rect_div a r) = mondrian_rect_width r ∧
      a * mondrian_rect_height (mondrian_rect_div a r) = mondrian_rect_height r := by
    intro r hr
    exact mondrian_rect_div_dimensions a ha r (hp.2.1 r hr).1
      (hp.2.1 r hr).2 (hd r hr).1 (hd r hr).2
  refine ⟨by simpa only [List.length_map] using hp.1, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have h1 := (hdim s hs).1
    have h2 := (hdim s hs).2
    have hpos := hp.2.1 s hs
    have hw : 0 < mondrian_rect_width (mondrian_rect_div a s) := by
      have : 0 < mondrian_rect_width s := Nat.sub_pos_of_lt hpos.1
      exact Nat.pos_of_mul_pos_left (by rwa [h1])
    have hh : 0 < mondrian_rect_height (mondrian_rect_div a s) := by
      have : 0 < mondrian_rect_height s := Nat.sub_pos_of_lt hpos.2
      exact Nat.pos_of_mul_pos_left (by rwa [h2])
    exact ⟨Nat.lt_of_sub_pos hw, Nat.lt_of_sub_pos hh⟩
  · rw [List.pairwise_map]
    apply hp.2.2.1.imp_of_mem
    intro r s hr hs hrs
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro ⟨i, j⟩ hi hj
      exact Finset.disjoint_left.mp hrs.1
        ((mondrian_rect_div_cells a ha r i j).mp hi)
        ((mondrian_rect_div_cells a ha s i j).mp hj)
    · intro hc
      apply hrs.2
      obtain ⟨hrw, hrh⟩ := hdim r hr
      obtain ⟨hsw, hsh⟩ := hdim s hs
      rcases hc with ⟨hw, hh⟩ | ⟨hw, hh⟩
      · left
        constructor
        · rw [← hrw, ← hsw, hw]
        · rw [← hrh, ← hsh, hh]
      · right
        constructor
        · rw [← hrw, ← hsh, hw]
        · rw [← hrh, ← hsw, hh]
  · ext ⟨i, j⟩
    constructor
    · intro hi
      obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      have hi' := (mondrian_rect_div_cells a ha s i j).mp hi
      have hu : (a * (i + 1) - 1, a * (j + 1) - 1) ∈
          P.toFinset.biUnion mondrian_rect_cells :=
        Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hs, hi'⟩
      rw [hp.2.2.2] at hu
      simp only [Finset.mem_product, Finset.mem_range] at hu ⊢
      have hiq := (mondrian_interval_div a 0 (a * c) i ha).mpr ⟨Nat.zero_le _, hu.1⟩
      have hjq := (mondrian_interval_div a 0 (a * c) j ha).mpr ⟨Nat.zero_le _, hu.2⟩
      simpa only [Nat.mul_div_cancel_left c ha] using And.intro hiq.2 hjq.2
    · intro hi
      simp only [Finset.mem_product, Finset.mem_range] at hi
      have hi1 := (mondrian_interval_div a 0 (a * c) i ha).mp
        ⟨by simp, by simpa only [Nat.mul_div_cancel_left c ha] using hi.1⟩
      have hi2 := (mondrian_interval_div a 0 (a * c) j ha).mp
        ⟨by simp, by simpa only [Nat.mul_div_cancel_left c ha] using hi.2⟩
      have hu : (a * (i + 1) - 1, a * (j + 1) - 1) ∈
          Finset.range (a * c) ×ˢ Finset.range (a * c) := by
        simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨hi1.2, hi2.2⟩
      rw [← hp.2.2.2] at hu
      obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hu
      apply Finset.mem_biUnion.mpr
      refine ⟨mondrian_rect_div a r, ?_, (mondrian_rect_div_cells a ha r i j).mpr hm⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩)
