import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide
import AFTD.Kb.Tcs.BoolSumEqCardFilter
import AFTD.Kb.Tcs.CyclePowerGapSidesDisjoint

/-!
# cycle_power_gap_sides_card

Topic: combinatorics   Node: 7b9db1c3f6c8

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

If r is below g, g is at most D, and every selected offset of a radius-D profile is localized below absolute vertex g or at least D, its selected-offset count equals the sum of its two compressed side sizes.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_gap_sides_card
    (D g r : ℕ) (hg : g ≤ D) (hr : r < g) (b : ℕ → Bool)
    (hgap : ∀ a < D, b a = true → r+a < g ∨ D ≤ r+a) :
    (range D).sum (fun a => (b a).toNat) =
      (cycle_power_gap_left_side g r b).card + (cycle_power_gap_right_side D g r b).card := by
  classical
  rw [bool_sum_eq_card_filter, ← card_union_of_disjoint (cycle_power_gap_sides_disjoint D g r b)]
  let S := (range D).filter (fun a => b a = true)
  let f (a : ℕ) (ha : a ∈ S) : Fin g :=
    ⟨if r+a < D then r+a else r+a-D, by
      have haD := mem_range.mp (mem_filter.mp ha).1
      have hba := (mem_filter.mp ha).2
      have hga := hgap a haD hba
      split_ifs with h
      · omega
      · omega⟩
  change S.card = _
  apply card_bij f
  · intro a ha
    have haD := mem_range.mp (mem_filter.mp ha).1
    have hba := (mem_filter.mp ha).2
    have hga := hgap a haD hba
    by_cases h : r+a < D
    · apply mem_union.mpr
      left
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_, ?_⟩
      · dsimp [f]
        rw [if_pos h]
        omega
      · have he : (f a ha).val-r = a := by dsimp [f]; rw [if_pos h]; omega
        simpa only [he] using hba
    · apply mem_union.mpr
      right
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_, ?_⟩
      · dsimp [f]
        rw [if_neg h]
        omega
      · have he : D+(f a ha).val-r = a := by dsimp [f]; rw [if_neg h]; omega
        simpa only [he] using hba
  · intro a ha a' ha' he
    have heval := congrArg Fin.val he
    have haD := mem_range.mp (mem_filter.mp ha).1
    have ha'D := mem_range.mp (mem_filter.mp ha').1
    dsimp [f] at heval
    split_ifs at heval <;> omega
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · have hri := (mem_filter.mp hi).2.1
      have hbi := (mem_filter.mp hi).2.2
      have hiD : i.val < D := lt_of_lt_of_le i.isLt hg
      have ha : i.val-r ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hbi⟩
      refine ⟨i.val-r, ha, ?_⟩
      apply Fin.ext
      dsimp [f]
      rw [if_pos (by omega : r+(i.val-r) < D)]
      omega
    · have hir := (mem_filter.mp hi).2.1
      have hbi := (mem_filter.mp hi).2.2
      have ha : D+i.val-r ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hbi⟩
      refine ⟨D+i.val-r, ha, ?_⟩
      apply Fin.ext
      dsimp [f]
      rw [if_neg (by omega : ¬r+(D+i.val-r) < D)]
      omega
