import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_shape_bound

Topic: combinatorics   Node: 7a7633cdd454

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

A partition of the n-square whose rectangles all have area A has at most as many members as available unordered dimension pairs.
-/

theorem mondrian_shape_bound (n A : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : mondrian_is_partition n P)
    (hA : ∀ r ∈ P, mondrian_rect_area r = A) :
    P.length ≤ (mondrian_factor_shapes n A).card := by
  let f := fun r => (min (mondrian_rect_width r) (mondrian_rect_height r),
    max (mondrian_rect_width r) (mondrian_rect_height r))
  have hinj : ∀ r s, f r = f s → mondrian_rect_congruent r s := by
    intro r s he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp [f] at he1 he2
    unfold mondrian_rect_congruent
    omega
  have hn : (P.map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact h.2.2.1.imp (fun hh he => hh.2 (hinj _ _ he))
  have hsub : (P.map f).toFinset ⊆ mondrian_factor_shapes n A := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    obtain ⟨hx, hy, hw, hh, hwn, hhn⟩ := mondrian_partition_bounds n P h r hr
    apply (mondrian_mem_factor_shapes n A (f r)).mpr
    refine ⟨?_, ?_, by dsimp [f]; omega, by dsimp [f]; omega⟩
    · dsimp [f]
      rw [min_mul_max]
      exact hA r hr
    · rw [← hA r hr]
      exact Nat.ne_of_gt (Nat.mul_pos hw hh)
  have hc := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn, List.length_map] using hc
