import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCostLeAddItemWait
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineItemWaitExistsEqZero
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineItemWait
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment

/-!
# probabilistic_serial_line_distortion_le_of_item_wait_le

Topic: social_choice   Node: 4b84edfd0250

Provenance: helper lemma. Reduction step for OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

If on an instance (agents at a, items at b, distance rankings pref) every item's waiting cost is at most OPT, then the probabilistic serial cost is at most n * OPT.
-/

theorem probabilistic_serial_line_distortion_le_of_item_wait_le (n : ℕ) (a b : Fin n → ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) (h : is_line_distance_preference_profile a b pref)
    (hw : ∀ j, probabilistic_serial_line_item_wait b pref j ≤ line_min_matching_cost a b) :
    probabilistic_serial_line_cost a b pref ≤ n * line_min_matching_cost a b := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [probabilistic_serial_line_cost]
  · obtain ⟨j0, hj0⟩ := probabilistic_serial_line_item_wait_exists_eq_zero hn b pref
    have h1 := probabilistic_serial_line_cost_le_add_item_wait a b pref h
    have h2 : ∑ j, probabilistic_serial_line_item_wait b pref j =
        ∑ j ∈ Finset.univ.erase j0, probabilistic_serial_line_item_wait b pref j :=
      (Finset.sum_erase _ hj0).symm
    have h3 : ∑ j ∈ Finset.univ.erase j0, probabilistic_serial_line_item_wait b pref j ≤
        (Finset.univ.erase j0).card • line_min_matching_cost a b :=
      Finset.sum_le_card_nsmul _ _ _ (fun j _ => hw j)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one] at h3
    nlinarith
