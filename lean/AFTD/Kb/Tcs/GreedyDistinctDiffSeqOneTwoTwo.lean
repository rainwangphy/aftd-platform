import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyDistinctDiffSeq
import AFTD.Kb.Tcs.GreedyDistinctDiffNext

/-!
# greedy_distinct_diff_seq_one_two_two

Topic: combinatorics   Node: 7a6afd70ef03

Provenance: helper lemma. Sanity lemma for the definition of the greedy sequence, arXiv:2610.15860 (A note on the Slater–Vélez permutation) (the sequence 1, 2, 4, 7, 3, 8, …).

The greedy sequence started at 1, 2 has third term 4 (3 is refused since |3 − 2| = 1 is already a difference).
-/

theorem greedy_distinct_diff_seq_one_two_two : greedy_distinct_diff_seq 1 2 2 = 4 := by
  show greedy_distinct_diff_next [2, 1] = 4
  unfold greedy_distinct_diff_next
  apply le_antisymm
  · apply Nat.sInf_le
    simp
  · apply le_csInf ⟨4, by simp⟩
    rintro c ⟨hc0, hc1, hc2⟩
    simp at hc1 hc2
    omega
