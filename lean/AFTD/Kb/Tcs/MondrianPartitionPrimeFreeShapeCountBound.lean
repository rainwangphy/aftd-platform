import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_partition_prime_free_shape_count_bound

Topic: combinatorics   Node: 67751788f365

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

In an admissible equal-area partition, any selected collection of tiles each having a side indivisible by q has cardinality at most the number of available unordered shapes having such a side.
-/

theorem mondrian_partition_prime_free_shape_count_bound (n A q : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hA : ∀ r ∈ P, mondrian_rect_area r = A)
    (pred : (ℕ × ℕ × ℕ × ℕ) → Bool)
    (hpred : ∀ r ∈ P, pred r → ¬ q ∣ mondrian_rect_width r ∨ ¬ q ∣ mondrian_rect_height r) :
    P.countP pred ≤ ((mondrian_factor_shapes n A).filter
      (fun d => ¬ q ∣ d.1 ∨ ¬ q ∣ d.2)).card := by
  let f := fun r => (min (mondrian_rect_width r) (mondrian_rect_height r),
    max (mondrian_rect_width r) (mondrian_rect_height r))
  have hinj : ∀ r s, f r = f s → mondrian_rect_congruent r s := by
    intro r s he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp [f] at h1 h2
    unfold mondrian_rect_congruent
    omega
  have hn : ((P.filter pred).map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply (hP.2.2.1.filter pred).imp
    intro a b hh he
    exact hh.2 (hinj _ _ he)
  have hsub : ((P.filter pred).map f).toFinset ⊆ (mondrian_factor_shapes n A).filter
      (fun d => ¬ q ∣ d.1 ∨ ¬ q ∣ d.2) := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    obtain ⟨hrP, hrpred⟩ := List.mem_filter.mp hr
    obtain ⟨hx, hy, hw, hh, hwn, hhn⟩ := mondrian_partition_bounds n P hP r hrP
    apply Finset.mem_filter.mpr
    constructor
    · apply (mondrian_mem_factor_shapes n A (f r)).mpr
      refine ⟨?_, ?_, by dsimp [f]; omega, by dsimp [f]; omega⟩
      · dsimp [f]; rw [min_mul_max]; exact hA r hrP
      · rw [← hA r hrP]; exact Nat.ne_of_gt (Nat.mul_pos hw hh)
    · have ht := hpred r hrP hrpred
      dsimp [f]
      by_cases hwh : mondrian_rect_width r ≤ mondrian_rect_height r
      · simpa [min_eq_left hwh, max_eq_right hwh] using ht
      · simpa [min_eq_right (by omega : mondrian_rect_height r ≤ mondrian_rect_width r),
          max_eq_left (by omega : mondrian_rect_height r ≤ mondrian_rect_width r)] using ht.symm
  have hc := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn, List.length_map, ← List.countP_eq_length_filter] using hc
