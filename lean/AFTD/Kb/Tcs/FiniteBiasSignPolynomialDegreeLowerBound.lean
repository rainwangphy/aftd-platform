import AFTD.Prelude

/-!
# finite_bias_sign_polynomial_degree_lower_bound

Topic: quantum   Node: 5286a83d6395

Provenance: helper lemma. Elementary polynomial interpolation, used to assess the finite-error-spectrum route toward OP-1638.

If a real polynomial vanishes at zero and takes value one at m distinct real numbers, then its degree is at least m.
-/

/-- An odd signal polynomial that equalizes m distinct nonzero biases has degree at least m. -/
theorem finite_bias_sign_polynomial_degree_lower_bound (m : ℕ) (p : Polynomial ℝ)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (hzero : p.eval 0 = 0) (hlevels : ∀ i, p.eval (c i) = 1) :
    m ≤ p.natDegree := by
  by_contra hn
  have hn' : p.natDegree < m := Nat.lt_of_not_ge hn
  have hpoly : p = Polynomial.C (1 : ℝ) := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p (Polynomial.C (1 : ℝ)) hc
    · intro i
      simpa using hlevels i
    · simpa using hn'
  have := congrArg (Polynomial.eval (0 : ℝ)) hpoly
  simp [hzero] at this
