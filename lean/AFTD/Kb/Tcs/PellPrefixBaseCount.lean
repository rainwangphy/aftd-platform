import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountListConcat
import AFTD.Kb.Tcs.NfaRunCountListNil
import AFTD.Kb.Tcs.PellStepIff
import AFTD.Kb.Tcs.PellWordPrefix
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# pell_prefix_base_count

Topic: automata   Node: 6f43673e1dac

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The prefix c_1c_2 has 1 run from q_1 to q_2, 2 runs from q_1 to q_3, 1 run from q_1 to q_4, and no runs to any other state, in A_n.
-/

lemma pell_prefix_base_count_count_c1 (n : ℕ) (hn : 3 ≤ n) (s1 : Fin n) :
    nfa_run_count_list (pell_nfa n) ([] ++ [⟨1, by decide⟩]) ⟨0, by omega⟩ s1 =
      if s1.val = 0 ∨ s1.val = 2 then 1 else 0 := by
  rw [nfa_run_count_list_concat]
  simp_rw [nfa_run_count_list_nil]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · have h_iff : s1 ∈ (pell_nfa n).step ⟨0, by omega⟩ ⟨1, by decide⟩ ↔ s1.val = 0 ∨ s1.val = 2 := by
      rw [pell_step_iff n hn]
      change (1 = 0 % 5 ∧ 1 ≤ 0 ∧ 0 + 2 ≤ n ∧ (s1.val = 0 ∨ s1.val = 0 + 1)) ∨
        (1 = 0 % 5 ∧ 0 + 1 = n ∧ s1.val = 0) ∨
        (1 = (0 + 1) % 5 ∧ 0 + 3 ≤ n ∧ (s1.val = 0 ∨ s1.val = 0 + 2)) ∨
        (1 = (0 + 1) % 5 ∧ 0 + 2 = n ∧ s1.val = 0) ∨
        (1 = (0 + 2) % 5 ∧ 0 + 3 ≤ n ∧ (s1.val = 0 + 1 ∨ s1.val = 0 + 2)) ↔ s1.val = 0 ∨ s1.val = 2
      omega
    split_ifs <;> aesop
  · intro b _ hb
    split_ifs with h1 h2
    · subst h2; contradiction
    · rfl
    · rfl
  · intro h
    exact False.elim (h (Finset.mem_univ _))

lemma pell_prefix_base_count_sum_two_fin (n : ℕ) (hn : 3 ≤ n) (f : Fin n → ℕ)
    (h_zero : ∀ x : Fin n, x.val ≠ 0 → x.val ≠ 2 → f x = 0) :
    (∑ x : Fin n, f x) = f ⟨0, by omega⟩ + f ⟨2, by omega⟩ := by
  let q0 : Fin n := ⟨0, by omega⟩
  let q2 : Fin n := ⟨2, by omega⟩
  have hne : q0 ≠ q2 := by
    intro h
    have h2 : q0.val = q2.val := congrArg Fin.val h
    change 0 = 2 at h2
    contradiction
  have hsub : ({q0, q2} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have heq : (∑ x : Fin n, f x) = ∑ x ∈ ({q0, q2} : Finset (Fin n)), f x := by
    apply (Finset.sum_subset hsub _).symm
    intro x _ hx
    apply h_zero
    · intro h0
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      ext
      exact h0
    · intro h2
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      ext
      exact h2
  rw [heq, Finset.sum_pair hne]

lemma pell_prefix_base_count_step_q0_c2 (n : ℕ) (hn : 3 ≤ n) (s : Fin n) :
    s ∈ (pell_nfa n).step ⟨0, by omega⟩ ⟨2, by decide⟩ ↔ s.val = 1 ∨ s.val = 2 := by
  rw [pell_step_iff n hn]
  change (2 = 0 % 5 ∧ 1 ≤ 0 ∧ 0 + 2 ≤ n ∧ (s.val = 0 ∨ s.val = 0 + 1)) ∨
    (2 = 0 % 5 ∧ 0 + 1 = n ∧ s.val = 0) ∨
    (2 = (0 + 1) % 5 ∧ 0 + 3 ≤ n ∧ (s.val = 0 ∨ s.val = 0 + 2)) ∨
    (2 = (0 + 1) % 5 ∧ 0 + 2 = n ∧ s.val = 0) ∨
    (2 = (0 + 2) % 5 ∧ 0 + 3 ≤ n ∧ (s.val = 0 + 1 ∨ s.val = 0 + 2)) ↔ s.val = 1 ∨ s.val = 2
  omega

lemma pell_prefix_base_count_step_q2_c2 (n : ℕ) (hn : 3 ≤ n) (s : Fin n) :
    s ∈ (pell_nfa n).step ⟨2, by omega⟩ ⟨2, by decide⟩ ↔ s.val = 2 ∨ s.val = 3 := by
  rw [pell_step_iff n hn]
  change (2 = 2 % 5 ∧ 1 ≤ 2 ∧ 2 + 2 ≤ n ∧ (s.val = 2 ∨ s.val = 2 + 1)) ∨
    (2 = 2 % 5 ∧ 2 + 1 = n ∧ s.val = 2) ∨
    (2 = (2 + 1) % 5 ∧ 2 + 3 ≤ n ∧ (s.val = 2 ∨ s.val = 2 + 2)) ∨
    (2 = (2 + 1) % 5 ∧ 2 + 2 = n ∧ s.val = 2) ∨
    (2 = (2 + 2) % 5 ∧ 2 + 3 ≤ n ∧ (s.val = 2 + 1 ∨ s.val = 2 + 2)) ↔ s.val = 2 ∨ s.val = 3
  have : s.val < n := s.isLt
  omega

open Classical in
/-- After the first block the count vector of the prefix v_1 = c_1c_2 has exactly 1 run at state q_2, 2 runs at q_3 and 1 run at q_4, and nothing elsewhere. -/
theorem pell_prefix_base_count (n : ℕ) (hn : 3 ≤ n) (s : Fin n) :
    nfa_run_count_list (pell_nfa n) (pell_word_prefix 1) ⟨0, by omega⟩ s
      = (if s.val = 1 then 1 else 0) + (if s.val = 2 then 2 else 0)
        + (if s.val = 3 then 1 else 0) := by
  have hp : pell_word_prefix 1 = ([] ++ [⟨1, by decide⟩]) ++ [⟨2, by decide⟩] := rfl
  rw [hp, nfa_run_count_list_concat]
  simp_rw [pell_prefix_base_count_count_c1 n hn]
  let f : Fin n → ℕ := fun s1 =>
    if s ∈ (pell_nfa n).step s1 ⟨2, by decide⟩ then (if s1.val = 0 ∨ s1.val = 2 then 1 else 0) else 0
  change (∑ s1 : Fin n, f s1) = _
  rw [pell_prefix_base_count_sum_two_fin n hn f]
  · have h0 := pell_prefix_base_count_step_q0_c2 n hn s
    have h2 := pell_prefix_base_count_step_q2_c2 n hn s
    dsimp [f]
    split_ifs <;> (try tauto) <;> (try omega)
  · intro x h0 h2
    dsimp [f]
    split_ifs with h1 h3
    · cases h3 <;> contradiction
    · rfl
    · rfl
