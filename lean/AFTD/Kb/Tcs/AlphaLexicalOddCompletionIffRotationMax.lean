import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalOddCompletionIffRotationMaxOfPrime
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaLexicalLt

/-!
# alpha_lexical_odd_completion_iff_rotation_max

Topic: combinatorics   Node: 020bbb8e2f42

Provenance: helper lemma. The existing proof of alpha_lexical_odd_completion_iff_rotation_max_of_prime uses no primality hypothesis; the result is needed to check composite-degree examples arising from OP-392, arXiv:2610.24758.

For any length n at least three, a nonempty positive sequence of sum n−1 is lexical if and only if its odd-parity binary completion is nonconstant and has strictly greater inverse Gray rank than each of its nontrivial cyclic rotations. No primality assumption is required.
-/

theorem alpha_lexical_odd_completion_iff_rotation_max (n : ℕ)
    (hn3 : 3 ≤ n) (a : List ℕ) (hne : a ≠ [])
    (ha : ∀ v ∈ a, 0 < v) (hs : a.sum + 1 = n) :
    alpha_is_lexical a ↔
      let x := 2 * alpha_binary_prefix a + (a.length + 1) % 2
      0 < x ∧ x < 2 ^ n - 1 ∧
        ∀ r : ℕ, 0 < r → r < n →
          brgc_inverse n ((bitword_rotate n)^[r] x) < brgc_inverse n x := by
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one a.length with hev | hodd
  · rw [show (a.length + 1) % 2 = 1 by omega, alpha_rot_completion_even a]
    have hCpos : ∀ v ∈ a ++ [1], 0 < v := by
      intro v hv; rcases List.mem_append.mp hv with h | h
      · exact ha v h
      · simp at h; omega
    have hCsum : (a ++ [1]).sum = n := by simp; omega
    rw [← alpha_rot_glue n _ hCpos hCsum hn3, alpha_rot_core_even a hne ha hev]
    simp only [List.length_append, List.length_singleton]
    constructor
    · intro H k hk0 hk; rw [alpha_rot_even_R_eq a k (by omega)]; exact H k hk0 hk
    · intro H k hk0 hk; rw [← alpha_rot_even_R_eq a k (by omega)]; exact H k hk0 hk
  · rcases List.eq_nil_or_concat' a with h | ⟨a', c, rfl⟩
    · exact absurd h hne
    have hc : 0 < c := ha c (by simp)
    rw [show ((a' ++ [c]).length + 1) % 2 = 0 by omega, add_zero,
      alpha_rot_completion_odd a' c hc]
    have hCpos : ∀ v ∈ a' ++ [c + 1], 0 < v := by
      intro v hv; rcases List.mem_append.mp hv with h | h
      · exact ha v (by simp [h])
      · simp at h; omega
    have hCsum : (a' ++ [c + 1]).sum = n := by simp at hs ⊢; omega
    rw [← alpha_rot_glue n _ hCpos hCsum hn3, alpha_rot_core_odd a' c ha hodd]
    simp only [List.length_append, List.length_singleton]
