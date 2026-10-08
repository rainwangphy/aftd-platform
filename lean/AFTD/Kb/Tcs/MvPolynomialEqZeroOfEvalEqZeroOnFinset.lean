import AFTD.Prelude

/-!
# mv_polynomial_eq_zero_of_eval_eq_zero_on_finset

Topic: algebraic_complexity   Node: e9962903f777

Provenance: formalization of a published result. Source: Shpilka & Yehudayoff 2010, Lemma 2.1; Schwartz 1980; Zippel 1979

Let R be an integral domain and p be a multivariate polynomial in n variables over R. If S is a finite subset of R with cardinality strictly greater than the total degree of p, and p evaluates to zero at every point of the product S^n, then p is the zero polynomial.
-/

/-- A multivariate polynomial over an integral domain vanishing on a grid S^n with |S| > deg(p) is zero. -/
theorem mv_polynomial_eq_zero_of_eval_eq_zero_on_finset {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] (p : MvPolynomial (Fin n) R) (S : Finset R) (hcard : p.totalDegree < S.card) (h_eval : ∀ f : Fin n → R, (∀ i, f i ∈ S) → MvPolynomial.eval f p = 0) : p = 0 := by
  classical
  by_contra hp
  have h_sz := MvPolynomial.schwartz_zippel_totalDegree hp S
  have h_eq : {f ∈ Fintype.piFinset (fun (_ : Fin n) ↦ S) | MvPolynomial.eval f p = 0} = Fintype.piFinset (fun (_ : Fin n) ↦ S) := by
    apply Finset.filter_true_of_mem
    intro f hf
    apply h_eval
    intro i
    rw [Fintype.mem_piFinset] at hf
    exact hf i
  rw [h_eq] at h_sz
  rw [Fintype.card_piFinset] at h_sz
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h_sz
  push_cast at h_sz
  have hScard_pos : 0 < S.card := by omega
  have hpow_pos : (0 : ℚ≥0) < (S.card : ℚ≥0) ^ n := by positivity
  rw [div_self (ne_of_gt hpow_pos)] at h_sz
  have hS_pos : (0 : ℚ≥0) < (S.card : ℚ≥0) := by positivity
  have h_lt : (p.totalDegree : ℚ≥0) / (S.card : ℚ≥0) < 1 := by
    rw [div_lt_one hS_pos]
    exact Nat.cast_lt.mpr hcard
  exact not_le_of_gt h_lt h_sz
