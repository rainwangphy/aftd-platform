import AFTD.Prelude

/-!
# not_is_intersective_sq_add_one

Topic: elementary_number_theory   Node: 6046b6ead926

Provenance: helper lemma. folklore

The polynomial $X^2 + 1$ does not have an integer root modulo every positive integer (in particular modulo 3).
-/

/-- The polynomial X^2 + 1 does not have a root modulo every positive integer. -/
theorem not_is_intersective_sq_add_one :
    ¬ (∀ m : ℕ, 0 < m → ∃ n : ℤ, (Polynomial.X ^ 2 + 1 : Polynomial ℤ).eval n ≡ 0 [ZMOD m]) := by
  intro h
  obtain ⟨n, hn⟩ := h 3 (by norm_num)
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hn
  have hz : (n : ZMod 3) ^ 2 + 1 = 0 := by
    have h' : ((n ^ 2 + 1 : ℤ) : ZMod 3) = ((0 : ℤ) : ZMod 3) :=
      (ZMod.intCast_eq_intCast_iff (n ^ 2 + 1) 0 3).mpr hn
    push_cast at h' ⊢
    exact h'
  have hnone : ¬ ∃ x : ZMod 3, x ^ 2 + 1 = 0 := by decide
  exact hnone ⟨n, hz⟩
