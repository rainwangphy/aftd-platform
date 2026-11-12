import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeMaxPairCount

/-!
# bpe_greedy_step_length_le

Topic: algorithms   Node: c4f1e65ffb52

Provenance: helper lemma. arXiv:2611.08671

Any greedy full byte-pair merge step produces an output string of length at most the input string length.
-/

lemma bpe_greedy_step_length_le_full_merge (a b z : ℕ) (s : List ℕ) :
    (bpe_full_merge a b z s).length ≤ s.length := by
  induction s using bpe_full_merge.induct a b with
  | case1 => simp [bpe_full_merge]
  | case2 x => simp [bpe_full_merge]
  | case3 x y xs h ih =>
    rw [bpe_full_merge, if_pos h]
    simp only [List.length_cons]
    omega
  | case4 x y xs h ih =>
    rw [bpe_full_merge, if_neg h]
    simpa using ih

/-- A single greedy BPE merge step never increases the length of the string. -/
theorem bpe_greedy_step_length_le (s t : List ℕ) (h : bpe_greedy_step s t) : t.length ≤ s.length := by
  rcases h with ⟨-, rfl⟩ | ⟨a, b, z, -, -, -, rfl⟩
  · exact le_rfl
  · exact bpe_greedy_step_length_le_full_merge a b z s
