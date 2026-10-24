import AFTD.Prelude

/-!
# positive_coefficient_selected_linear_product

Topic: graphs   Node: 5917658a1680

Provenance: helper lemma. Helper for OP-494 in arXiv:2610.30174, following the additive-list coloring argument of arXiv:2302.02190v3, Corollary 5.3. Induct over the factors. In the coefficient convolution retain the positive term given by the selected monomials; all other terms are nonnegative.

Selecting a variable in each linear form with natural coefficients gives a positive coefficient of the corresponding product monomial.
-/

open scoped BigOperators
open MvPolynomial

theorem positive_coefficient_selected_linear_product
    {E V : Type*} [DecidableEq E] [DecidableEq V]
    (s : Finset E) (A : E → Finset V) (f : E → V)
    (hf : ∀ e ∈ s, f e ∈ A e) :
    0 < (∏ e ∈ s, (∑ w ∈ A e, X w : MvPolynomial V ℕ)).coeff
      (∑ e ∈ s, Finsupp.single (f e) 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s hes ih =>
    rw [Finset.prod_insert hes, Finset.sum_insert hes, coeff_mul]
    have hfirst : 0 < (∑ w ∈ A e, X w : MvPolynomial V ℕ).coeff
        (Finsupp.single (f e) 1) := by
      rw [coeff_sum]
      have hle := Finset.single_le_sum
        (fun w (_ : w ∈ A e) => Nat.zero_le
          ((X w : MvPolynomial V ℕ).coeff (Finsupp.single (f e) 1)))
        (hf e (Finset.mem_insert_self _ _))
      simpa using (lt_of_lt_of_le (by simp :
        0 < (X (f e) : MvPolynomial V ℕ).coeff (Finsupp.single (f e) 1)) hle)
    have hrest := ih (fun e he => hf e (Finset.mem_insert_of_mem he))
    apply lt_of_lt_of_le (Nat.mul_pos hfirst hrest)
    exact Finset.single_le_sum
      (f := fun p : (V →₀ ℕ) × (V →₀ ℕ) =>
        (∑ w ∈ A e, X w : MvPolynomial V ℕ).coeff p.1 *
        (∏ e ∈ s, ∑ w ∈ A e, X w : MvPolynomial V ℕ).coeff p.2)
      (a := (Finsupp.single (f e) 1, ∑ e ∈ s, Finsupp.single (f e) 1))
      (fun _ _ => Nat.zero_le _) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)
