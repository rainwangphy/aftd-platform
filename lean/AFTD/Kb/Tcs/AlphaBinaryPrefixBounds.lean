import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixAppend

/-!
# alpha_binary_prefix_bounds

Topic: combinatorics   Node: ac8ec5f192ca

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The encoding of a nonempty positive cell sequence has exactly sum(a) bits and starts with a one.
-/

theorem alpha_binary_prefix_bounds_lt (a : List ℕ) (ha : ∀ v ∈ a, 0 < v) :
    alpha_binary_prefix a < 2 ^ a.sum := by
  induction a with
  | nil => simp [alpha_binary_prefix]
  | cons x xs ih =>
    have hx : 0 < x := ha x (by simp)
    have hxs : ∀ v ∈ xs, 0 < v := fun v hv => ha v (by simp [hv])
    have ih' : alpha_binary_prefix xs < 2 ^ xs.sum := ih hxs
    rw [alpha_binary_prefix, List.sum_cons]
    have h1 : 2 ^ xs.sum ≤ 2 ^ (x - 1 + xs.sum) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : alpha_binary_prefix xs < 2 ^ (x - 1 + xs.sum) := lt_of_lt_of_le ih' h1
    have h3 : 2 ^ (x - 1 + xs.sum) + alpha_binary_prefix xs <
        2 ^ (x - 1 + xs.sum) + 2 ^ (x - 1 + xs.sum) :=
      Nat.add_lt_add_left h2 _
    have h4 : 2 ^ (x - 1 + xs.sum) + 2 ^ (x - 1 + xs.sum) = 2 ^ (x + xs.sum) := by
      rw [← Nat.two_pow_succ]
      congr 1
      omega
    exact lt_of_lt_of_eq h3 h4

theorem alpha_binary_prefix_bounds (a : List ℕ) (hne : a ≠ [])
    (ha : ∀ v ∈ a, 0 < v) :
    2 ^ (a.sum - 1) ≤ alpha_binary_prefix a ∧ alpha_binary_prefix a < 2 ^ a.sum := by
  refine ⟨?_, alpha_binary_prefix_bounds_lt a ha⟩
  match a, hne with
  | x :: xs, _ =>
    rw [alpha_binary_prefix, List.sum_cons]
    have hx : 0 < x := ha x (by simp)
    have he : x - 1 + xs.sum = x + xs.sum - 1 := by omega
    rw [he]
    exact Nat.le_add_right _ _
