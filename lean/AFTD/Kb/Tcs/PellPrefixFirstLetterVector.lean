import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountListConcat
import AFTD.Kb.Tcs.PellStepIff
import AFTD.Kb.Tcs.FinsetSumEqThreeOfOff
import AFTD.Kb.Tcs.PellWordPrefix
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.PellNumber
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# pell_prefix_first_letter_vector

Topic: automata   Node: 52f490ca4ac2

Provenance: helper lemma. step towards pell_prefix_block_step

After appending only the letter c_(i+1) to the prefix, the run counts are P(i+1)-P(i) at q_i, 2P(i) at q_(i+1), (P(i+1)-P(i))+2P(i) at q_(i+2), and vanish at every other state.
-/

open Classical in
/-- One-letter DP step: appending the single letter c_(i+1) to `pell_word_prefix i` maps the vector (x at q_i, y at q_(i+1)), vanishing off q_i,q_(i+1),q_(i+2), to (x at q_i, y at q_(i+1), x+y at q_(i+2)), zero everywhere else. -/
theorem pell_prefix_first_letter_vector (n i : ℕ) (hn : 3 ≤ n) (h1 : 1 ≤ i) (hi : i + 1 ≤ n - 2)
    (hzero : ∀ s : Fin n, s.val ≠ i → s.val ≠ i + 1 → s.val ≠ i + 2 →
      nfa_run_count_list (pell_nfa n) (pell_word_prefix i) ⟨0, by omega⟩ s = 0)
    (hx : nfa_run_count_list (pell_nfa n) (pell_word_prefix i) ⟨0, by omega⟩
      ⟨i, by omega⟩ = pell_number (i + 1) - pell_number i)
    (hy : nfa_run_count_list (pell_nfa n) (pell_word_prefix i) ⟨0, by omega⟩
      ⟨i + 1, by omega⟩ = 2 * pell_number i) (s : Fin n) :
    nfa_run_count_list (pell_nfa n) (pell_word_prefix i ++ [⟨(i + 1) % 5, by omega⟩])
        ⟨0, by omega⟩ s
      = (if s.val = i then (pell_number (i + 1) - pell_number i) else 0)
        + (if s.val = i + 1 then (2 * pell_number i) else 0)
        + (if s.val = i + 2 then ((pell_number (i + 1) - pell_number i) + 2 * pell_number i) else 0) := by
  have h_step_i : s ∈ (pell_nfa n).step ⟨i, by omega⟩ ⟨(i + 1) % 5, by omega⟩ ↔ (s.val = i ∨ s.val = i + 2) := by
    have h := @pell_step_iff n hn ⟨i, by omega⟩ s ⟨(i + 1) % 5, by omega⟩
    dsimp at h
    rw [h]
    constructor
    · rintro (⟨hmod, -⟩ | ⟨hmod, -⟩ | ⟨-, -, hq⟩ | ⟨-, h2, -⟩ | ⟨hmod, -⟩)
      · exfalso; omega
      · exfalso; omega
      · exact hq
      · exfalso; omega
      · exfalso; omega
    · intro hq
      right; right; left
      refine ⟨rfl, by omega, hq⟩
  have h_step_ip1 : s ∈ (pell_nfa n).step ⟨i + 1, by omega⟩ ⟨(i + 1) % 5, by omega⟩ ↔ (s.val = i + 1 ∨ s.val = i + 2) := by
    have h := @pell_step_iff n hn ⟨i + 1, by omega⟩ s ⟨(i + 1) % 5, by omega⟩
    dsimp at h
    rw [h]
    constructor
    · rintro (⟨-, -, -, hq⟩ | ⟨-, h2, -⟩ | ⟨hmod, -⟩ | ⟨hmod, -⟩ | ⟨hmod, -⟩)
      · exact hq
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    · intro hq
      left
      refine ⟨rfl, by omega, by omega, hq⟩
  have h_step_ip2 : s ∉ (pell_nfa n).step ⟨i + 2, by omega⟩ ⟨(i + 1) % 5, by omega⟩ := by
    have h := @pell_step_iff n hn ⟨i + 2, by omega⟩ s ⟨(i + 1) % 5, by omega⟩
    dsimp at h
    rw [h]
    rintro (⟨hmod, -⟩ | ⟨hmod, -⟩ | ⟨hmod, -⟩ | ⟨hmod, -⟩ | ⟨hmod, -⟩) <;> (exfalso; omega)

  rw [nfa_run_count_list_concat]
  let g : Fin n → ℕ := fun t =>
    if s ∈ (pell_nfa n).step t ⟨(i + 1) % 5, by omega⟩
    then nfa_run_count_list (pell_nfa n) (pell_word_prefix i) ⟨0, by omega⟩ t else 0
  change (∑ t : Fin n, g t) = _
  have hab : (⟨i, by omega⟩ : Fin n) ≠ ⟨i + 1, by omega⟩ := by intro h; injection h with h; omega
  have hac : (⟨i, by omega⟩ : Fin n) ≠ ⟨i + 2, by omega⟩ := by intro h; injection h with h; omega
  have hbc : (⟨i + 1, by omega⟩ : Fin n) ≠ ⟨i + 2, by omega⟩ := by intro h; injection h with h; omega
  rw [finset_sum_eq_three_of_off g hab hac hbc]
  · dsimp [g]
    rw [hx, hy]
    rw [if_congr h_step_i rfl rfl]
    rw [if_congr h_step_ip1 rfl rfl]
    rw [if_neg h_step_ip2]
    split_ifs <;> omega
  · intro t hti htip1 htip2
    dsimp [g]
    have hzt : nfa_run_count_list (pell_nfa n) (pell_word_prefix i) ⟨0, by omega⟩ t = 0 := by
      apply hzero t
      · intro h; apply hti; ext; exact h
      · intro h; apply htip1; ext; exact h
      · intro h; apply htip2; ext; exact h
    rw [hzt]
    split_ifs <;> rfl
