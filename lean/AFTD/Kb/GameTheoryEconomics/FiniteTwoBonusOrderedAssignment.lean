import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteTwoBonusAssignment

/-!
# finite_two_bonus_ordered_assignment

Topic: fair_division   Node: cf15f1d8c06b

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For any finite nonempty real matrix w and two nonnegative agent-dependent bonuses a and b, there is a permutation of the old columns, a recipient r of a, and a recipient s of b, possibly equal, which weakly improves each original diagonal. Removing a from column r or b from column s leaves no foreign envy toward that column relative to the final own values.
-/

open Function Finset

theorem finite_two_bonus_ordered_assignment {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (w : α → α → ℝ) (a b : α → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∃ (p : Equiv.Perm α) (r s : α),
      (∀ i, w i i ≤ w i (p i) + (if i = r then a i else 0) + (if i = s then b i else 0)) ∧
      (∀ i, i ≠ r → w i (p r) + (if r = s then b i else 0) ≤
        w i (p i) + (if i = r then a i else 0) + (if i = s then b i else 0)) ∧
      (∀ i, i ≠ s → w i (p s) + (if s = r then a i else 0) ≤
        w i (p i) + (if i = r then a i else 0) + (if i = s then b i else 0)) := by
  let g : Bool → α → ℝ := fun t => if t then b else a
  have hg (t : Bool) (i : α) : 0 ≤ g t i := by cases t <;> simp [g, ha, hb]
  obtain ⟨p, r, s, t, hI, hA, hB⟩ := finite_two_bonus_assignment w g hg
  cases t
  · exact ⟨p, r, s, by simpa [g] using hI, by simpa [g] using hA, by simpa [g] using hB⟩
  · refine ⟨p, s, r, ?_, ?_, ?_⟩
    · simpa [g, add_comm, add_left_comm, add_assoc] using hI
    · simpa [g, add_comm, add_left_comm, add_assoc] using hB
    · simpa [g, add_comm, add_left_comm, add_assoc] using hA
