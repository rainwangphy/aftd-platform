import AFTD.Prelude

/-!
# quadratic_func_at_most_two_roots

Topic: combinatorics   Node: 7deb318e5dbd

Provenance: helper lemma. folklore

A nonzero quadratic polynomial t ↦ A * t^2 + B * t + C with A ≠ 0 has at most two real roots.
-/

/-- A nonzero quadratic polynomial has at most two real roots. -/
theorem quadratic_func_at_most_two_roots (A B C : ℝ) (hA : A ≠ 0) (s : Finset ℝ)
    (hs : ∀ t ∈ s, A * t ^ 2 + B * t + C = 0) : s.card ≤ 2 := by
  let p : Polynomial ℝ := Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X + Polynomial.C C
  have hp : p ≠ 0 := by
    intro h
    have hc := congr_arg (Polynomial.coeff · 2) h
    simp [p] at hc
    exact hA hc
  have hroots : s.val ⊆ p.roots := by
    intro t ht
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    have heval : p.eval t = A * t ^ 2 + B * t + C := by simp [p]
    rw [heval]
    exact hs t ht
  have hdeg : p.natDegree ≤ 2 := by
    refine Polynomial.natDegree_add_le_of_degree_le ?_ (by simp)
    refine Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_C_mul_X_pow_le A 2) ?_
    have h1 := Polynomial.natDegree_C_mul_X_pow_le B 1
    simp only [pow_one] at h1
    omega
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  exact hcard.trans hdeg
