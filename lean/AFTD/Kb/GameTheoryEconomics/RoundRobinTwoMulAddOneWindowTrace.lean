import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateCardDiffStepOfNe
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateSuccStep
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceGetElemEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateUpdateOfNotMemTake
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState

/-!
# round_robin_two_mul_add_one_window_trace

Topic: fair_division   Node: e6ae5c69330c

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

Round-Robin with n agents and 2n+1 goods: change only agent i's report to r. Then at every time s between i's first turn and i's second turn (i <= s <= i + n), the goods allocated by the deviated run and by the original run differ in at most one element each way.
-/

theorem round_robin_two_mul_add_one_window_trace_mod (n s : ℕ) (i : ℕ) (hi : i < n) (h1 : i < s)
    (h2 : s < i + n) : s % n ≠ i := by
  rcases Nat.lt_or_ge s n with hs | hs
  · rw [Nat.mod_eq_of_lt hs]; omega
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]; omega

/-- Over the window between agent i's two Round-Robin turns, the original and the deviated run have allocated sets differing in at most one element on each side. -/
theorem round_robin_two_mul_add_one_window_trace (n : ℕ) [NeZero n]
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1)) (i : Fin n)
    (r : Fin (2 * n + 1) ≃ Fin (2 * n + 1)) :
    ∀ s, i.val ≤ s → s ≤ i.val + n →
      ((picking_prefix_state (round_robin_sequence n (2 * n + 1)) (Function.update rank i r) s).2 \
        (picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank s).2).card ≤ 1 ∧
      ((picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank s).2 \
        (picking_prefix_state (round_robin_sequence n (2 * n + 1)) (Function.update rank i r) s).2).card ≤ 1 := by
  have hlen : (round_robin_sequence n (2 * n + 1)).length = 2 * n + 1 := by
    simp [round_robin_sequence]
  have hi := i.isLt
  have h0 : picking_prefix_state (round_robin_sequence n (2 * n + 1)) (Function.update rank i r) i.val =
      picking_prefix_state (round_robin_sequence n (2 * n + 1)) rank i.val := by
    apply picking_prefix_state_update_of_not_mem_take
    intro hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨t, ht, he⟩ := hmem
    rw [List.length_take] at ht
    rw [List.getElem_take] at he
    have hget := round_robin_sequence_getElem?_eq n (2 * n + 1) t (by omega)
    rw [List.getElem?_eq_getElem (by omega), he, Option.some_inj] at hget
    have := congrArg Fin.val hget
    simp only at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  intro s hs1 hs2
  induction s, hs1 using Nat.le_induction with
  | base => rw [h0]; simp
  | succ s hs ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hsl : s < (round_robin_sequence n (2 * n + 1)).length := by omega
    have ha := round_robin_sequence_getElem?_eq n (2 * n + 1) s (by omega)
    rcases hs.lt_or_eq with hlt | heq
    · exact picking_prefix_state_card_diff_step_of_ne _ rank i r s (by omega) hsl (by omega) _ ha
        (by
          intro hc
          have := congrArg Fin.val hc
          simp only at this
          exact round_robin_two_mul_add_one_window_trace_mod n s i.val hi hlt (by omega) this)
        ih1 ih2
    · subst heq
      have hai : (⟨i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := by
        ext; simp [Nat.mod_eq_of_lt hi]
      rw [hai] at ha
      obtain ⟨p, -, hA', -⟩ := picking_prefix_state_succ_step _ (Function.update rank i r) i.val hsl
        (by omega) i ha
      obtain ⟨q, -, hB', -⟩ := picking_prefix_state_succ_step _ rank i.val hsl (by omega) i ha
      rw [hA', hB', h0]
      constructor
      · refine (Finset.card_le_card (t := {p}) ?_).trans (by simp)
        intro z hz
        simp only [Finset.mem_sdiff, Finset.mem_insert] at hz
        rcases hz with ⟨rfl | hz, hn⟩
        · simp
        · exact absurd (Or.inr hz) hn
      · refine (Finset.card_le_card (t := {q}) ?_).trans (by simp)
        intro z hz
        simp only [Finset.mem_sdiff, Finset.mem_insert] at hz
        rcases hz with ⟨rfl | hz, hn⟩
        · simp
        · exact absurd (Or.inr hz) hn
