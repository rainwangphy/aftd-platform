import AFTD.Prelude
import AFTD.Kb.Tcs.PositiveCoefficientSelectedLinearProduct

/-!
# exists_signed_nonzero_linear_forms

Topic: graphs   Node: e3821e924f93

Provenance: helper lemma. Helper for OP-494 in arXiv:2610.30174, following the additive-list coloring argument of arXiv:2302.02190v3, Corollary 5.3. Map the positive-coefficient natural polynomial to the integers, compare its degree with the selected exponent sum, and apply the polynomial nonvanishing theorem.

A family of sums of variables admits a simultaneous nonzero evaluation on finite integer lists whose sizes exceed the selection multiplicities.
-/

open scoped BigOperators
open MvPolynomial

theorem exists_signed_nonzero_linear_forms
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (A : E → Finset V) (f : E → V) (hf : ∀ e, f e ∈ A e)
    (L : V → Finset ℤ)
    (hL : ∀ v, (Finset.univ.filter (fun e => f e = v)).card < (L v).card) :
    ∃ x : V → ℤ, (∀ v, x v ∈ L v) ∧ ∀ e, ∑ w ∈ A e, x w ≠ 0 := by
  classical
  let t : V →₀ ℕ := ∑ e : E, Finsupp.single (f e) 1
  let P : MvPolynomial V ℕ := ∏ e : E, ∑ w ∈ A e, X w
  let Q : MvPolynomial V ℤ := ∏ e : E, ∑ w ∈ A e, X w
  have hmap : Q = MvPolynomial.map (Nat.castRingHom ℤ) P := by
    simp [P, Q]
  have ht : Q.coeff t ≠ 0 := by
    rw [hmap, coeff_map]
    have h := positive_coefficient_selected_linear_product Finset.univ A f
      (fun e _ => hf e)
    change 0 < P.coeff t at h
    intro hz
    exact (Nat.ne_of_gt h) (Int.ofNat_inj.mp hz)
  have htdeg : t.degree = Fintype.card E := by
    simp [t, map_sum, Finsupp.degree_single]
  have hupper : Q.totalDegree ≤ Fintype.card E := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      (∑ e : E, (∑ w ∈ A e, (X w : MvPolynomial V ℤ)).totalDegree) ≤
          ∑ _e : E, 1 := by
        apply Finset.sum_le_sum
        intro e _
        apply (MvPolynomial.totalDegree_finsetSum _ _).trans
        apply Finset.sup_le
        intro w _
        simp
      _ = Fintype.card E := by simp
  have hdeg : Q.totalDegree = t.degree := by
    apply le_antisymm
    · simpa only [htdeg] using hupper
    · change t.sum (fun _ n => n) ≤ Q.totalDegree
      exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr ht)
  have htL : ∀ v, t v < (L v).card := by
    intro v
    have hval : t v = (Finset.univ.filter (fun e => f e = v)).card := by
      simp only [t, Finsupp.finsetSum_apply, Finsupp.single_apply,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hval]
    exact hL v
  obtain ⟨x, hx, hnonzero⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero Q t ht hdeg L htL
  refine ⟨x, hx, ?_⟩
  have hprod : (∏ e : E, ∑ w ∈ A e, x w) ≠ 0 := by
    simpa [Q] using hnonzero
  exact fun e => (Finset.prod_ne_zero_iff.mp hprod) e (Finset.mem_univ _)
