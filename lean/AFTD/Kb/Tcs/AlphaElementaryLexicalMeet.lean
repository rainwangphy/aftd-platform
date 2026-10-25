import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalMeetIsLexical

/-!
# alpha_elementary_lexical_meet

Topic: combinatorics   Node: a93ce6dab1ff

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Proposed helper discharging the lexical common-prefix hypothesis in the published adjacency criterion for a valid negative-cell elementary operation.
-/

theorem alpha_elementary_lexical_meet_aux_meet (p s t : List ℕ) (x y : ℕ) (hxy : x ≠ y) :
    alpha_lexical_meet (p ++ x :: s) (p ++ y :: t) = p ++ [min x y] := by
  induction p with
  | nil => simp [alpha_lexical_meet, hxy]
  | cons z p ih => simp [alpha_lexical_meet, ih]

theorem alpha_elementary_lexical_meet (a b : List ℕ) (i : ℕ)
    (ha : alpha_is_lexical a) (hb : alpha_is_lexical b)
    (hi : i % 2 = 1) (hstep : alpha_elementary_cell_step a b i) :
    alpha_is_lexical (alpha_lexical_meet a b) ∧
      1 < (alpha_lexical_meet a b).sum + 1 ∧
      (alpha_lexical_meet a b).sum + 1 < a.sum + 1 := by
  obtain ⟨hane, hapos, halex⟩ := ha
  obtain ⟨hl, hstep'⟩ := hstep
  have hlex : alpha_is_lexical (alpha_lexical_meet a b) :=
    alpha_lexical_meet_is_lexical a b ⟨hane, hapos, halex⟩ hb
  rcases hstep' with ⟨hgt, hbeq⟩ | ⟨hipos, h1, hbeq⟩
  · have hdrop : List.drop i a = a.getD i 0 :: List.drop (i + 1) a := by
      rw [List.getD_eq_getElem a 0 hl, List.drop_eq_getElem_cons hl]
    have haeq : a = List.take i a ++ (a.getD i 0 :: List.drop (i + 1) a) := by
      have h := List.take_append_drop i a
      rw [hdrop] at h
      exact h.symm
    have hbeq' : b = List.take i a ++ ((a.getD i 0 - 1) :: (1 :: List.drop (i + 1) a)) := by
      rw [hbeq]; simp
    have hmin : min (a.getD i 0) (a.getD i 0 - 1) = a.getD i 0 - 1 := by omega
    have hmeet : alpha_lexical_meet a b = List.take i a ++ [a.getD i 0 - 1] := by
      conv_lhs => rw [haeq, hbeq']
      rw [alpha_elementary_lexical_meet_aux_meet (List.take i a) (List.drop (i + 1) a)
          (1 :: List.drop (i + 1) a) (a.getD i 0) (a.getD i 0 - 1) (by omega), hmin]
    have hsum_meet : (alpha_lexical_meet a b).sum = (List.take i a).sum + (a.getD i 0 - 1) := by
      rw [hmeet]; simp
    have hsum_a : a.sum = (List.take i a).sum + a.getD i 0 + (List.drop (i + 1) a).sum := by
      conv_lhs => rw [haeq]
      simp [Nat.add_assoc]
    exact ⟨hlex, by rw [hsum_meet]; omega, by rw [hsum_meet, hsum_a]; omega⟩
  · have hlt1 : i - 1 < a.length := by omega
    have hsub : i - 1 + 1 = i := by omega
    have hdrop1 : List.drop (i - 1) a =
        a.getD (i - 1) 0 :: (a.getD i 0 :: List.drop (i + 1) a) := by
      rw [List.getD_eq_getElem a 0 hlt1, List.drop_eq_getElem_cons hlt1, hsub,
        List.getD_eq_getElem a 0 hl, List.drop_eq_getElem_cons hl]
    have haeq : a = List.take (i - 1) a ++
        (a.getD (i - 1) 0 :: (a.getD i 0 :: List.drop (i + 1) a)) := by
      have h := List.take_append_drop (i - 1) a
      rw [hdrop1] at h
      exact h.symm
    have hbeq' : b = List.take (i - 1) a ++ ((a.getD (i - 1) 0 + 1) :: List.drop (i + 1) a) := by
      rw [hbeq]; simp
    have hmeet : alpha_lexical_meet a b = List.take (i - 1) a ++ [a.getD (i - 1) 0] := by
      conv_lhs => rw [haeq, hbeq']
      rw [alpha_elementary_lexical_meet_aux_meet (List.take (i - 1) a)
          (a.getD i 0 :: List.drop (i + 1) a) (List.drop (i + 1) a) (a.getD (i - 1) 0)
          (a.getD (i - 1) 0 + 1) (by omega), Nat.min_eq_left (by omega)]
    have hsum_meet : (alpha_lexical_meet a b).sum = (List.take (i - 1) a).sum + a.getD (i - 1) 0 := by
      rw [hmeet]; simp
    have hsum_a : a.sum = (List.take (i - 1) a).sum + a.getD (i - 1) 0 + a.getD i 0 +
        (List.drop (i + 1) a).sum := by
      conv_lhs => rw [haeq]
      simp [Nat.add_assoc]
    have hypos : 0 < a.getD (i - 1) 0 :=
      hapos _ (by rw [List.getD_eq_getElem a 0 hlt1]; exact List.getElem_mem hlt1)
    exact ⟨hlex, by rw [hsum_meet]; omega, by rw [hsum_meet, hsum_a]; omega⟩
