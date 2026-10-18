import AFTD.Prelude
import AFTD.Kb.Tcs.FiveDiamondLevelColoring

/-!
# five_diamond_level_coloring_interval_card_le_three

Topic: combinatorics   Node: 8d28963ca711

Provenance: helper lemma. step towards op_270_five_diamond_poset_ramsey_number

Let k ≥ 1 and d ≤ 4k-1. If B ⊂ T are subsets of Fin d with min (k-1) (|B|/4) = min (k-1) (|T|/4), then |T \ B| ≤ 3.
-/

/-- Two sets of the same level-colour, the smaller contained in the larger, differ in at most 3 points when the ground set has at most 4k-1 elements. -/
theorem five_diamond_level_coloring_interval_card_le_three (k d : ℕ) (hk : 1 ≤ k)
    (hd : d ≤ 4 * k - 1) (B T : Finset (Fin d)) (hBT : B ⊂ T)
    (hcol : five_diamond_level_coloring k d hk B = five_diamond_level_coloring k d hk T) :
    (T \ B).card ≤ 3 := by
  have hval : min (k - 1) (B.card / 4) = min (k - 1) (T.card / 4) := by
    have := congrArg Fin.val hcol
    simpa [five_diamond_level_coloring] using this
  rw [Finset.card_sdiff_of_subset hBT.subset]
  have hTB : B.card ≤ T.card := Finset.card_le_card hBT.subset
  have hTc : T.card ≤ d := by
    have := T.card_le_univ; simpa using this
  rcases Nat.lt_or_ge (T.card / 4) (k - 1) with hlt | hge
  · have hTmin : min (k - 1) (T.card / 4) = T.card / 4 := Nat.min_eq_right (Nat.le_of_lt hlt)
    rw [hTmin] at hval
    have hBle : B.card / 4 ≤ T.card / 4 := Nat.div_le_div_right hTB
    have hBeq : B.card / 4 = T.card / 4 := by
      have : T.card / 4 ≤ B.card / 4 := hval ▸ Nat.min_le_right _ _
      omega
    omega
  · have hTmin : min (k - 1) (T.card / 4) = k - 1 := Nat.min_eq_left hge
    rw [hTmin] at hval
    have hBge : k - 1 ≤ B.card / 4 := hval ▸ Nat.min_le_right _ _
    omega
