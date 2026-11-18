import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# alpha_last_blocking_suffix_is_lexical

Topic: combinatorics   Node: dbdd196bf5a2

Provenance: helper lemma. Last-blocker reduction for OP-392, arXiv:2610.24758; alternating lexical order as in arXiv:0810.5205.

For a positive sequence, its last suffix that is not smaller than the sequence is lexical.
-/

theorem alpha_lbs_signed_zero (A : List ℕ) (j : ℕ) (h : A.length ≤ j) :
    alpha_signed_cell A j = 0 := by
  unfold alpha_signed_cell
  rw [List.getD_eq_default _ _ h]; split_ifs <;> simp

theorem alpha_lbs_lt_of_ne (A B : List ℕ) (p : ℕ)
    (heq : ∀ j < p, alpha_signed_cell A j = alpha_signed_cell B j)
    (hlt : alpha_signed_cell A p < alpha_signed_cell B p) : alpha_lexical_lt A B := by
  refine ⟨p, ?_, heq, hlt⟩
  by_contra hp
  push Not at hp
  rw [alpha_lbs_signed_zero A p (le_trans (le_max_left _ _) hp),
    alpha_lbs_signed_zero B p (le_trans (le_max_right _ _) hp)] at hlt
  exact lt_irrefl _ hlt

theorem alpha_lbs_lt_of_lt_of_not_lt (X C D : List ℕ) (hX : alpha_lexical_lt X C)
    (hD : ¬ alpha_lexical_lt D C) : alpha_lexical_lt X D := by
  classical
  obtain ⟨p, _, hpre, hp⟩ := hX
  by_cases hex : ∃ q, alpha_signed_cell D q ≠ alpha_signed_cell C q
  · have hq := Nat.find_spec hex
    have hqmin : ∀ j < Nat.find hex, alpha_signed_cell D j = alpha_signed_cell C j := by
      intro j hj
      by_contra hne
      exact Nat.find_min hex hj hne
    set q := Nat.find hex
    have hgt : alpha_signed_cell C q < alpha_signed_cell D q := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact absurd (alpha_lbs_lt_of_ne D C q hqmin h) hD
      · exact h
    rcases lt_trichotomy p q with h | h | h
    · apply alpha_lbs_lt_of_ne X D p
      · intro j hj; rw [hpre j hj, hqmin j (lt_trans hj h)]
      · rw [hqmin p h]; exact hp
    · rw [h] at hp hpre
      apply alpha_lbs_lt_of_ne X D q
      · intro j hj; rw [hpre j hj, hqmin j hj]
      · exact lt_trans hp hgt
    · apply alpha_lbs_lt_of_ne X D q
      · intro j hj; rw [hpre j (lt_trans hj h), hqmin j hj]
      · rw [hpre q h]; exact hgt
  · push Not at hex
    apply alpha_lbs_lt_of_ne X D p
    · intro j hj; rw [hpre j hj, hex j]
    · rw [hex p]; exact hp

theorem alpha_last_blocking_suffix_is_lexical (c : List ℕ) (s : ℕ) (hpos : ∀ v ∈ c, 0 < v) (hs0 : 0 < s) (hs : s < c.length) (hbad : ¬ alpha_lexical_lt (c.drop s) c) (hlast : ∀ t : ℕ, s < t → t < c.length → alpha_lexical_lt (c.drop t) c) : alpha_is_lexical (c.drop s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp at this; omega
  · intro v hv
    exact hpos v (List.mem_of_mem_drop hv)
  · intro k hk hk0
    simp only [List.length_drop] at hk
    rw [List.drop_drop]
    exact alpha_lbs_lt_of_lt_of_not_lt _ _ _ (hlast (s + k) (by omega) (by omega)) hbad
