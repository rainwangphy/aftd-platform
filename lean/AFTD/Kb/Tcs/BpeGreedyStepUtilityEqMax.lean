import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeMaxPairCount

/-!
# bpe_greedy_step_utility_eq_max

Topic: algorithms   Node: 008b19f3e1ce

Provenance: helper lemma. Helper for the two-merge case of OP-1287 and arXiv:2611.08671v1, Theorem 12.

A greedy full-merge step decreases the string length by exactly the maximum nonoverlapping adjacent-pair count, including the unchanged step when this count is zero.
-/

private lemma op1287_full_merge_length_le
    (a b z : ℕ) (s : List ℕ) : (bpe_full_merge a b z s).length ≤ s.length := by
  refine bpe_full_merge.induct a b (fun s => (bpe_full_merge a b z s).length ≤ s.length) ?_ ?_ ?_ ?_ s
  · simp [bpe_full_merge]
  · intro x
    simp [bpe_full_merge]
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = z :: bpe_full_merge a b z xs := by
      simp [bpe_full_merge, hxy]
    rw [hm]
    simp only [List.length_cons] at ih ⊢
    omega
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = x :: bpe_full_merge a b z (y :: xs) := by
      simp [bpe_full_merge, hxy]
    rw [hm]
    simp only [List.length_cons] at ih ⊢
    omega

private lemma op1287_full_merge_length_sub
    (a b z : ℕ) (s : List ℕ) :
    s.length - (bpe_full_merge a b z s).length = bpe_pair_count a b s := by
  refine bpe_full_merge.induct a b (fun s => s.length - (bpe_full_merge a b z s).length = bpe_pair_count a b s) ?_ ?_ ?_ ?_ s
  · simp [bpe_full_merge, bpe_pair_count]
  · intro x
    simp [bpe_full_merge, bpe_pair_count]
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = z :: bpe_full_merge a b z xs := by
      simp [bpe_full_merge, hxy]
    have hc : bpe_pair_count a b (x :: y :: xs) = 1 + bpe_pair_count a b xs := by
      simp [bpe_pair_count, hxy]
    rw [hm, hc]
    simp only [List.length_cons] at ih ⊢
    have hle := op1287_full_merge_length_le a b z xs
    omega
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = x :: bpe_full_merge a b z (y :: xs) := by
      simp [bpe_full_merge, hxy]
    have hc : bpe_pair_count a b (x :: y :: xs) = bpe_pair_count a b (y :: xs) := by
      simp [bpe_pair_count, hxy]
    rw [hm, hc]
    simp only [List.length_cons] at ih ⊢
    have hle := op1287_full_merge_length_le a b z (y :: xs)
    simp only [List.length_cons] at hle
    omega

theorem bpe_greedy_step_utility_eq_max
    (s t : List ℕ) (h : bpe_greedy_step s t) :
    s.length - t.length = bpe_max_pair_count s := by
  rcases h with ⟨hmax, rfl⟩ | ⟨a, b, z, hpos, hcount, hz, rfl⟩
  · simp [hmax]
  · rw [op1287_full_merge_length_sub, hcount]
