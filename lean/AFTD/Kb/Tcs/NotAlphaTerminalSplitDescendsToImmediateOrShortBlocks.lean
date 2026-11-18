import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction
import AFTD.Kb.Tcs.AlphaDescent35TerminalHypotheses
import AFTD.Kb.Tcs.AlphaDescent35NoProposedShortExit

/-!
# not_alpha_terminal_split_descends_to_immediate_or_short_blocks

Topic: combinatorics   Node: b0ae345402ff

Provenance: original. Related work: Finite counterexample to the internal helper alpha_terminal_split_descends_to_immediate_or_short_blocks for OP-392, arXiv:2610.24758; it does not refute the prime main statement.

It is false that every lexical sequence a and positive even index i in its bounds, with a[i]>1, a lexical prefix a.take i, a nonlexical split at i, and no later lexical even elementary move, has an even index j with i<=j<a.length satisfying one of the following. Let f be a.take j with a[j]-1 appended when a[j]>1, and otherwise a.take j; let u=a.take(j+1); let v be f with its last cell increased when f has even length, and otherwise f followed by 1. Either f is lexical and a equals u followed by f or by v then f, or a[j]>1, a.take j is lexical, and, for c=a.take j ++ [a[j]-1,1] ++ a.drop(j+1), both j+2<c.length and c.drop(j+2) is not strictly less than c in the lexical order.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem not_alpha_terminal_split_descends_to_immediate_or_short_blocks : ¬ (∀ (a : List ℕ) (i : ℕ) (ha : alpha_is_lexical a) (hi0 : 0 < i) (hi : i < a.length) (he : i % 2 = 0) (hc : 1 < a.getD i 0) (hp : alpha_is_lexical (a.take i)) (hfail : ¬ alpha_is_lexical (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1))) (hnone : ∀ j : ℕ, i < j → j % 2 = 0 → ∀ b : List ℕ, alpha_elementary_cell_step a b j → ¬ alpha_is_lexical b), ∃ j : ℕ, i ≤ j ∧ j < a.length ∧ j % 2 = 0 ∧ (let f := if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1] else a.take j; let u := a.take (j + 1); let v := if f.length % 2 = 0 then f.dropLast ++ [f.getLastD 0 + 1] else f ++ [1]; (alpha_is_lexical f ∧ (a = u ++ f ∨ a = u ++ v ++ f)) ∨ (1 < a.getD j 0 ∧ alpha_is_lexical (a.take j) ∧ (let c := a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1); j + 2 < c.length ∧ ¬ alpha_lexical_lt (c.drop (j + 2)) c)))) := by
  intro h
  let a : List ℕ := [2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1]
  have hcert := alpha_descent35_terminal_hypotheses
  dsimp only at hcert
  have ha : alpha_is_lexical a := hcert.1
  have hp : alpha_is_lexical (a.take 2) := hcert.2.2.1
  have hf : ¬ alpha_is_lexical (a.take 2 ++ [a.getD 2 0 - 1, 1] ++ a.drop 3) := by
    simpa [a] using hcert.2.2.2.1
  have hnone : ∀ j : ℕ, 2 < j → j % 2 = 0 → ∀ b : List ℕ,
      alpha_elementary_cell_step a b j → ¬ alpha_is_lexical b := by
    intro j hj he b hb
    rcases hb with ⟨hjlen, hsplit | hconj⟩
    · rcases hsplit with ⟨hgt, rfl⟩
      have hf := hcert.2.2.2.2 ⟨j, by simpa [a] using hjlen⟩ hj he
      have hgt' : 1 < ([2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1] : List ℕ).getD j 0 := by
        simpa only [a] using hgt
      simpa only [if_pos hgt'] using hf
    · rcases hconj with ⟨_, hcell, rfl⟩
      have hf := hcert.2.2.2.2 ⟨j, by simpa [a] using hjlen⟩ hj he
      have hneg : ¬ 1 < ([2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1] : List ℕ).getD j 0 := by
        have : ¬ 1 < a.getD j 0 := by omega
        simpa only [a] using this
      simpa only [if_neg hneg] using hf
  obtain ⟨j, hji, hjl, hje, hconcl⟩ := h a 2 ha (by decide) (by decide)
    (by decide) (by decide) hp hf hnone
  have hno := alpha_descent35_no_proposed_short_exit ⟨j, by simpa [a] using hjl⟩ hji hje
  dsimp only at hconcl hno
  rcases hconcl with hshort | ⟨hgt, hpref, hlen, hbad⟩
  · exact hno.1 hshort
  · have hgt' : 1 < ([2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1] : List ℕ).getD j 0 := by
      simpa only [a] using hgt
    simp only [if_pos hgt'] at hno
    exact hno.2 ⟨hgt, hpref, hlen, hbad⟩
