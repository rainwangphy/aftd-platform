import AFTD.Prelude
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# quantitative_combinatorial_nullstellensatz

Topic: graphs   Node: b30f5c4c58ac

Provenance: formalization of a published result. Source: arXiv:2610.41820 Lemma 2.1

For a multivariate polynomial f of total degree at most ∑ t_i over a field F, the coefficient of the monomial ∏ x_i^{t_i} equals the sum over points a in the grid ∏ S_i of f(a) divided by ∏_i ∏_{b ∈ S_i \ {a_i}} (a_i - b), where each S_i has cardinality t_i + 1.
-/

private lemma quantitative_combinatorial_nullstellensatz_sum_weight {F : Type*} [Field F] [DecidableEq F]
    (t : ℕ) (S : Finset F) (hS : S.card = t + 1) {k : ℕ} (hk : k ≤ t) :
    (∑ a ∈ S, a ^ k / ∏ b ∈ S.erase a, (a - b)) = if k = t then 1 else 0 := by
  have hdeg : (Polynomial.X ^ k : Polynomial F).degree < (S.card : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow, hS]
    exact_mod_cast Nat.lt_succ_iff.mpr hk
  have h := Lagrange.coeff_eq_sum (s := S) (v := fun x : F => x) (P := Polynomial.X ^ k)
    Function.injective_id.injOn hdeg
  simpa [hS, hk, Polynomial.coeff_X_pow, eq_comm] using h

private lemma quantitative_combinatorial_nullstellensatz_sum_pi_prod {σ F : Type*}
    [Fintype σ] [DecidableEq σ] [Field F] (S : σ → Finset F)
    (f : (i : σ) → S i → F) :
    (∑ a : (i : σ) → S i, ∏ i, f i (a i)) = ∏ i, ∑ a : S i, f i a := by
  classical
  rw [← Fintype.piFinset_univ (β := fun i : σ => S i)]
  rw [← Finset.prod_univ_sum (fun i : σ => (Finset.univ : Finset (S i))) f]

private lemma quantitative_combinatorial_nullstellensatz_exists_lt {σ : Type*} [Fintype σ]
    {v t : σ → ℕ} (hsum : ∑ i, v i ≤ ∑ i, t i) (hne : v ≠ t) :
    ∃ i, v i < t i := by
  classical
  by_contra h
  push_neg at h
  have hle : ∑ i, t i ≤ ∑ i, v i := Finset.sum_le_sum fun i _ => h i
  have heq : ∑ i, t i = ∑ i, v i := le_antisymm hle hsum
  have hall : ∀ i, t i = v i := by
    simpa using (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := t) (g := v) (fun i _ => h i)).mp heq
  exact hne (funext fun i => (hall i).symm)

private lemma quantitative_combinatorial_nullstellensatz_pi_weight_product {σ F : Type*}
    [Fintype σ] [DecidableEq σ] [Field F] [DecidableEq F]
    (t : σ → ℕ) (S : σ → Finset F) (hS : ∀ i, (S i).card = t i + 1)
    (v : σ →₀ ℕ) (hsum : v.sum (fun _ e => e) ≤ ∑ i, t i) :
    (∏ i : σ, ∑ x : S i,
       (x : F) ^ (v i) / ∏ b ∈ (S i).erase (x : F), ((x : F) - b)) =
    if v = Finsupp.equivFunOnFinite.symm t then 1 else 0 := by
  classical
  by_cases hv : v = Finsupp.equivFunOnFinite.symm t
  · subst hv
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    have h := quantitative_combinatorial_nullstellensatz_sum_weight (t i) (S i) (hS i)
      (le_rfl : t i ≤ t i)
    rw [if_pos rfl] at h
    exact (Finset.sum_finset_coe
      (fun a : F => a ^ (t i) / ∏ b ∈ (S i).erase a, (a - b)) (S i)).trans h
  · have hvfun : (fun i => v i) ≠ t := by
      intro h
      apply hv
      ext i
      exact congrFun h i
    have hsum' : ∑ i, v i ≤ ∑ i, t i := by
      simpa [Finsupp.sum_fintype] using hsum
    obtain ⟨j, hj⟩ := quantitative_combinatorial_nullstellensatz_exists_lt hsum' hvfun
    have hfac : (∑ x : S j,
        (x : F) ^ (v j) / ∏ b ∈ (S j).erase (x : F), ((x : F) - b)) = 0 := by
      have h := quantitative_combinatorial_nullstellensatz_sum_weight (t j) (S j) (hS j)
        (Nat.le_of_lt hj)
      rw [if_neg (ne_of_lt hj)] at h
      exact (Finset.sum_finset_coe
        (fun a : F => a ^ (v j) / ∏ b ∈ (S j).erase a, (a - b)) (S j)).trans h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hfac, if_neg hv]

private lemma quantitative_combinatorial_nullstellensatz_monomial_weighted_eval {σ F : Type*}
    [Fintype σ] [DecidableEq σ] [Field F] [DecidableEq F]
    (t : σ → ℕ) (S : σ → Finset F) (hS : ∀ i, (S i).card = t i + 1)
    (v : σ →₀ ℕ) (c : F) (hsum : v.sum (fun _ e => e) ≤ ∑ i, t i) :
    (∑ a : (i : σ) → S i,
       MvPolynomial.eval (fun i => (a i : F)) (MvPolynomial.monomial v c) /
       (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b))) =
    if v = Finsupp.equivFunOnFinite.symm t then c else 0 := by
  classical
  let f : (i : σ) → S i → F := fun i x =>
    (x : F) ^ (v i) / ∏ b ∈ (S i).erase (x : F), ((x : F) - b)
  have hterm : ∀ a : (i : σ) → S i,
      MvPolynomial.eval (fun i => (a i : F)) (MvPolynomial.monomial v c) /
        (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)) =
      c * ∏ i, f i (a i) := by
    intro a
    dsimp [f]
    rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
    rw [div_eq_mul_inv, Finset.prod_div_distrib]
    ring
  calc
    (∑ a : (i : σ) → S i,
       MvPolynomial.eval (fun i => (a i : F)) (MvPolynomial.monomial v c) /
       (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)))
        = ∑ a : (i : σ) → S i, c * ∏ i, f i (a i) := by
          exact Finset.sum_congr rfl fun a _ => hterm a
    _ = c * ∑ a : (i : σ) → S i, ∏ i, f i (a i) := by rw [Finset.mul_sum]
    _ = c * ∏ i : σ, ∑ x : S i, f i x := by
          rw [quantitative_combinatorial_nullstellensatz_sum_pi_prod]
    _ = c * (if v = Finsupp.equivFunOnFinite.symm t then 1 else 0) := by
          have hprod : (∏ i : σ, ∑ x : S i, f i x) =
              if v = Finsupp.equivFunOnFinite.symm t then 1 else 0 := by
            dsimp [f]
            exact quantitative_combinatorial_nullstellensatz_pi_weight_product t S hS v hsum
          rw [hprod]
    _ = if v = Finsupp.equivFunOnFinite.symm t then c else 0 := by
          split_ifs <;> simp

/-- Quantitative Combinatorial Nullstellensatz coefficient interpolation formula over finite grids in a field. -/
theorem quantitative_combinatorial_nullstellensatz {σ F : Type*} [Fintype σ] [DecidableEq σ] [Field F] [DecidableEq F]
    (t : σ → ℕ) (S : σ → Finset F) (hS : ∀ i, (S i).card = t i + 1)
    (f : MvPolynomial σ F) (hdeg : f.totalDegree ≤ ∑ i, t i) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm t) f =
      ∑ a : (i : σ) → S i,
        (MvPolynomial.eval (fun i => (a i : F)) f) /
        (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)) := by
  classical
  have hcoeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm t) f =
      ∑ v ∈ f.support,
        if v = Finsupp.equivFunOnFinite.symm t then MvPolynomial.coeff v f else 0 := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [MvPolynomial.coeff_monomial]
  have hsum_rhs :
      (∑ a : (i : σ) → S i,
        (MvPolynomial.eval (fun i => (a i : F)) f) /
        (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b))) =
      ∑ v ∈ f.support,
        if v = Finsupp.equivFunOnFinite.symm t then MvPolynomial.coeff v f else 0 := by
    have h_eval_sum : ∀ a : (i : σ) → S i,
        MvPolynomial.eval (fun i => (a i : F)) f =
          ∑ v ∈ f.support,
            MvPolynomial.eval (fun i => (a i : F))
              (MvPolynomial.monomial v (MvPolynomial.coeff v f)) := by
      intro a
      conv_lhs => rw [MvPolynomial.as_sum f]
      exact map_sum (MvPolynomial.eval (fun i => (a i : F)))
        (fun v => MvPolynomial.monomial v (MvPolynomial.coeff v f)) f.support
    calc
      (∑ a : (i : σ) → S i,
        (MvPolynomial.eval (fun i => (a i : F)) f) /
        (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)))
          = ∑ a : (i : σ) → S i,
              ∑ v ∈ f.support,
                (MvPolynomial.eval (fun i => (a i : F))
                  (MvPolynomial.monomial v (MvPolynomial.coeff v f))) /
                (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [h_eval_sum a, Finset.sum_div]
      _ = ∑ v ∈ f.support,
              ∑ a : (i : σ) → S i,
                (MvPolynomial.eval (fun i => (a i : F))
                  (MvPolynomial.monomial v (MvPolynomial.coeff v f))) /
                (∏ i : σ, ∏ b ∈ (S i).erase (a i), ((a i : F) - b)) := by
            rw [Finset.sum_comm]
      _ = ∑ v ∈ f.support,
              if v = Finsupp.equivFunOnFinite.symm t then MvPolynomial.coeff v f else 0 := by
            apply Finset.sum_congr rfl
            intro v hv
            exact quantitative_combinatorial_nullstellensatz_monomial_weighted_eval t S hS v
              (MvPolynomial.coeff v f) (le_trans (MvPolynomial.le_totalDegree hv) hdeg)
  rw [hcoeff, hsum_rhs]
