import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyRun
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpeGreedyStepWith
import AFTD.Kb.Tcs.BpeMaxPairCount

/-!
# bpe_greedy_run_length_lower_bound

Topic: algorithms   Node: 3363d52d804e

Provenance: helper lemma. step towards op_1533_iid_binary_greedy_bpe_universal_rate

Applying k greedy full BPE merges reduces the string length by at most a factor of 2^k: if bpe_greedy_run k s t, then s.length ≤ 2^k * t.length.
-/

lemma bpe_greedy_run_length_lower_bound_full_merge_le (a b z : ℕ) (s : List ℕ) :
    s.length ≤ 2 * (bpe_full_merge a b z s).length := by
  induction s using bpe_full_merge.induct a b with
  | case1 =>
    simp [bpe_full_merge.eq_1]
  | case2 head =>
    simp [bpe_full_merge.eq_2]
  | case3 x y xs hxy ih =>
    rw [bpe_full_merge.eq_3]
    have : (if x = a ∧ y = b then z :: bpe_full_merge a b z xs else x :: bpe_full_merge a b z (y :: xs)) =
      z :: bpe_full_merge a b z xs := if_pos hxy
    rw [this]
    simp only [List.length_cons] at *
    omega
  | case4 x y xs hxy ih =>
    rw [bpe_full_merge.eq_3]
    have : (if x = a ∧ y = b then z :: bpe_full_merge a b z xs else x :: bpe_full_merge a b z (y :: xs)) =
      x :: bpe_full_merge a b z (y :: xs) := if_neg hxy
    rw [this]
    simp only [List.length_cons] at *
    omega

lemma bpe_greedy_run_length_lower_bound_step_with_le (z : ℕ) (s t : List ℕ)
    (h : bpe_greedy_step_with z s t) : s.length ≤ 2 * t.length := by
  rcases h with ⟨-, rfl⟩ | ⟨a, b, -, -, rfl⟩
  · omega
  · exact bpe_greedy_run_length_lower_bound_full_merge_le a b z s

/-- Applying k greedy full BPE merges reduces the string length by at most a factor of 2^k, because each non-overlapping pair merge reduces string length by at most half. -/
theorem bpe_greedy_run_length_lower_bound (k : ℕ) (s t : List ℕ) (h : bpe_greedy_run k s t) : s.length ≤ 2^k * t.length := by
  induction k generalizing s t with
  | zero =>
    rw [bpe_greedy_run.eq_1] at h
    subst h
    simp
  | succ k ih =>
    rw [bpe_greedy_run.eq_2] at h
    rcases h with ⟨u, hsu, hut⟩
    have h1 := ih s u hsu
    have h2 := bpe_greedy_run_length_lower_bound_step_with_le (k + 2) u t hut
    calc s.length ≤ 2^k * u.length := h1
    _ ≤ 2^k * (2 * t.length) := Nat.mul_le_mul_left _ h2
    _ = 2^(k + 1) * t.length := by ring
