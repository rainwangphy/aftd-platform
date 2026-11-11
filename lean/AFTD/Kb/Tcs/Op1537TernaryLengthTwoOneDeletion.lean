import AFTD.Prelude
import AFTD.Kb.Tcs.IsWordRun
import AFTD.Kb.Tcs.IsLongestWordRun
import AFTD.Kb.Tcs.WordAbsorbRun
import AFTD.Kb.Tcs.QaryMultipleDeletionHinge
import AFTD.Kb.Tcs.IsConstantWord
import AFTD.Kb.Tcs.Op1534TernaryLengthTwoOneDeletion
import AFTD.Kb.Tcs.DecidableIsConstantWord
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# op_1537_ternary_length_two_one_deletion

Topic: information   Node: aa4077a526df

Provenance: original. Related work: knowledgebase (OP-1537, OP-1534)

For any nonconstant ternary word y : Fin 2 → Fin 3 of length 2, there exists a longest run [a, b) of y and an immediately adjacent run [a', b') of y such that the word y' obtained by changing every letter in [a', b') to y a satisfies qary_multiple_deletion_hinge 1 3 2 r y ≤ qary_multiple_deletion_hinge 1 3 2 r y' for all r ≥ 1, with strict inequality for at least one r ≥ 1.
-/

/-- OP-1537 for ternary words of length 2 with one deletion (n = 2, q = 3, t = 1). -/
theorem op_1537_ternary_length_two_one_deletion
    (y : Fin 2 → Fin 3) (hy : ¬ is_constant_word y) :
    ∃ (a b : ℕ) (hR : is_longest_word_run y a b) (a' b' : ℕ) (hR' : is_word_run y a' b')
      (hadj : b' = a ∨ b = a') (ha : a < 2),
      let y' := word_absorb_run y a' b' (y ⟨a, ha⟩)
      (∀ r : ℕ, 1 ≤ r → qary_multiple_deletion_hinge 1 3 2 r y ≤ qary_multiple_deletion_hinge 1 3 2 r y') ∧
      (∃ r : ℕ, 1 ≤ r ∧ qary_multiple_deletion_hinge 1 3 2 r y < qary_multiple_deletion_hinge 1 3 2 r y') := by
  have hnc_vals : ∀ (z : Fin 2 → Fin 3), ¬ is_constant_word z →
      qary_multiple_deletion_hinge 1 3 2 1 z = 2 ∧ qary_multiple_deletion_hinge 1 3 2 2 z = 0 := by decide
  have hc_vals : ∀ (z : Fin 2 → Fin 3), is_constant_word z →
      qary_multiple_deletion_hinge 1 3 2 1 z = 2 ∧ qary_multiple_deletion_hinge 1 3 2 2 z = 1 := by decide
  have hzero : ∀ (z : Fin 2 → Fin 3) (r : ℕ), 3 ≤ r → qary_multiple_deletion_hinge 1 3 2 r z = 0 := by
    intro z r hr
    have hbound : ∀ (x : Fin 3 → Fin 3) (w : Fin 2 → Fin 3),
        q_ary_subsequence_num_embeddings 3 2 3 w x ≤ 3 := by decide
    unfold qary_multiple_deletion_hinge
    apply Finset.sum_eq_zero
    intro x _
    apply Nat.sub_eq_zero_of_le
    exact le_trans (hbound x z) hr
  have hne : y ⟨0, by norm_num⟩ ≠ y ⟨1, by norm_num⟩ := by
    intro h
    apply hy
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  have hR : is_longest_word_run y 0 1 := by
    have hrun : is_word_run y 0 1 := by
      refine ⟨by norm_num, by norm_num, ?_, Or.inl rfl, Or.inr ⟨by norm_num, Ne.symm hne⟩⟩
      intro i hi
      obtain ⟨-, hi2⟩ := hi
      have hi0 : i = ⟨0, by norm_num⟩ := by
        apply Fin.ext
        simp only
        omega
      rw [hi0]
    refine ⟨hrun, ?_⟩
    intro a' b' hr'
    obtain ⟨hab, hbn, hconst, -, -⟩ := hr'
    simp only [Nat.sub_zero]
    by_contra h
    have h2 : 1 < b' - a' := not_le.mp h
    have ha' : a' = 0 := by omega
    have hb' : b' = 2 := by omega
    subst ha'
    subst hb'
    have h1 : y ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩ := by
      have := hconst ⟨1, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      simpa using this
    exact hne h1.symm
  have hR' : is_word_run y 1 2 := by
    refine ⟨by norm_num, by norm_num, ?_, Or.inr ⟨by norm_num, hne⟩, Or.inl rfl⟩
    intro i hi
    obtain ⟨hi1, -⟩ := hi
    have hii : i = ⟨1, by norm_num⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hii]
  refine ⟨0, 1, hR, 1, 2, hR', Or.inr rfl, by norm_num, ?_⟩
  dsimp only
  have hy'const : is_constant_word (word_absorb_run y 1 2 (y ⟨0, by norm_num⟩)) := by
    intro i j
    have hi : ∀ i : Fin 2, word_absorb_run y 1 2 (y ⟨0, by norm_num⟩) i = y ⟨0, by norm_num⟩ := by
      intro i
      fin_cases i <;> simp [word_absorb_run]
    rw [hi i, hi j]
  constructor
  · intro r hr
    rcases lt_or_ge r 3 with h3 | h3
    · have : r = 1 ∨ r = 2 := by omega
      rcases this with rfl | rfl
      · rw [(hnc_vals y hy).1, (hc_vals _ hy'const).1]
      · rw [(hnc_vals y hy).2, (hc_vals _ hy'const).2]
        norm_num
    · rw [hzero y r h3]
      exact Nat.zero_le _
  · refine ⟨2, by norm_num, ?_⟩
    rw [(hnc_vals y hy).2, (hc_vals _ hy'const).2]
    norm_num
