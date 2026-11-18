import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell

/-!
# alpha_signed_prefix_of_lexical_interval

Topic: combinatorics   Node: 58a2c0fbcf6e

Provenance: helper lemma. First-difference helper for the lexical route to OP-392, arXiv:2610.24758, using the order in arXiv:0810.5205.

If two sequences agree in their first i signed cells, and a third is below the first sequence but not below the second in alternating order, then the third also agrees in those first i signed cells, provided the second sequence has at least i cells.
-/

theorem alpha_signed_prefix_of_lexical_interval (u a c : List ℕ) (i : ℕ) (hc : i ≤ c.length) (hu : alpha_lexical_lt u a) (hn : ¬ alpha_lexical_lt u c) (hac : ∀ j < i, alpha_signed_cell a j = alpha_signed_cell c j) : ∀ j < i, alpha_signed_cell u j = alpha_signed_cell a j := by
  obtain ⟨q, hq, hprev, hlt⟩ := hu
  have hiq : i ≤ q := by
    by_contra H
    have hqi : q < i := by omega
    apply hn
    refine ⟨q, by omega, ?_, ?_⟩
    · intro j hj
      rw [← hac j (by omega)]
      exact hprev j hj
    · rw [← hac q hqi]
      exact hlt
  intro j hj
  exact hprev j (by omega)
