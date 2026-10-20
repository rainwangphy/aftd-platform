import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153CardLeOfAvoidingDiff

/-!
# op_153_card_le_of_poly_diff_free

Topic: elementary_number_theory   Node: ea0b9404c909

Provenance: helper lemma. arXiv:2610.07765 Sec. 1, line 244 -- A new bound for the Furstenberg--Sárközy theorem using the van der Corput property

Let $h \in \mathbb{Z}[X]$ be an integer polynomial such that $h(1) = k > 0$. Every subset $A \subseteq \{1, \dots, 2k\}$ whose distinct elements have difference not equal to $h(n)$ for any positive integer $n$ satisfies $|A| \le k$.
-/

/-- For any polynomial h with h(1) = k > 0, any h-difference-free subset of {1, ..., 2k} has size at most k. -/
theorem op_153_card_le_of_poly_diff_free (h : Polynomial ℤ) (k : ℕ) (hk : 0 < k)
    (heval : h.eval (1 : ℤ) = (k : ℤ)) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 (2 * k))
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = h.eval (n : ℤ)) :
    A.card ≤ k := by
  apply op_153_card_le_of_avoiding_diff k hk A hA
  intro a ha b hb hab hsub
  have hcontra := hdiff a ha b hb hab
  apply hcontra
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [Nat.cast_one, heval, hsub]
