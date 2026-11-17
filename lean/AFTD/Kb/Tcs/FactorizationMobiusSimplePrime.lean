import AFTD.Prelude
import AFTD.Kb.Tcs.FactorizationMobiusToTop
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.FactorizationCoarseningSignedOrderingsSumZero
import AFTD.Kb.Tcs.IsFactorizationCoarseningCardLtIffNe
import AFTD.Kb.Tcs.IsFactorizationCoarseningRefl
import AFTD.Kb.Tcs.SetOfIsNatFactorizationFinite
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# factorization_mobius_simple_prime

Topic: combinatorics   Node: c933c5aa1ec1

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Theorem 1 (first formula)

Theorem 1 of arXiv:2611.18194. Let n = mq where q is a prime not dividing m, and let x be a factorization of n (a multiset of integers greater than 1 with product n) with k factors. Let c_1, ..., c_s be the multiplicities in x of the distinct factors of x that are not divisible by q. Then μ(x, n) = (-1)^{k-1} (k-1)!/(c_1! ⋯ c_s!), the right side computed as a rational number, where μ(x, n) = factorizationMobiusToTop n x is the Möbius function of the poset of factorizations of n ordered by refinement (x ≤ y when y is a coarsening of x, IsFactorizationCoarsening x y), between x and the top element.
-/

namespace FactMobT1

noncomputable def fw (q : ℕ) (y : Multiset ℕ) : ℚ :=
  (-1 : ℚ) ^ (y.card - 1) * ((y.card - 1).factorial : ℚ) /
    ∏ a ∈ (y.filter (fun a => ¬ q ∣ a)).toFinset,
      (((y.filter (fun a => ¬ q ∣ a)).count a).factorial : ℚ)

lemma one_lt_prod_of {g : Multiset ℕ} (hg : g ≠ 0) (h : ∀ a ∈ g, 1 < a) : 1 < g.prod := by
  induction g using Multiset.induction_on with
  | empty => exact absurd rfl hg
  | cons a g ih =>
    rw [Multiset.prod_cons]
    have ha := h a (Multiset.mem_cons_self a g)
    have hp : 0 < g.prod := Multiset.prod_pos (fun b hb => by
      have := h b (Multiset.mem_cons_of_mem hb); omega)
    nlinarith

lemma coars_fact {n : ℕ} {x y : Multiset ℕ} (hx : IsNatFactorization n x)
    (h : IsFactorizationCoarsening x y) : IsNatFactorization n y := by
  obtain ⟨G, hG0, hJ, hM⟩ := h
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [← hM, Multiset.mem_map] at hb
    obtain ⟨g, hg, rfl⟩ := hb
    refine one_lt_prod_of (hG0 g hg) (fun a ha => hx.1 a ?_)
    rw [← hJ]; exact Multiset.mem_join.2 ⟨g, hg, ha⟩
  · rw [← hM, ← Multiset.prod_join, hJ]; exact hx.2

theorem thm1 (m q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m) (x : Multiset ℕ)
    (hx : IsNatFactorization (m * q) x) :
    (factorizationMobiusToTop (m * q) x : ℚ) = fw q x := by
  induction hk : x.card using Nat.strong_induction_on generalizing x with
  | _ k ih =>
  rw [factorizationMobiusToTop]
  split_ifs with h1
  · have hx0 : x ≠ 0 := by
      rintro rfl
      have h2 := hx.2
      simp only [Multiset.prod_zero] at h2
      have := hq.two_le
      have : m * q ≠ 1 := by
        intro h; have := Nat.eq_one_of_mul_eq_one_left h; omega
      exact this h2.symm
    obtain ⟨a, rfl⟩ : ∃ a, x = {a} :=
      Multiset.card_eq_one.1 (by have := Multiset.card_pos.2 hx0; omega)
    have ha : a = m * q := by simpa using hx.2
    subst ha
    unfold fw
    simp [Multiset.filter_singleton, dvd_mul_left]
  · have hsq : ¬ q ^ 2 ∣ x.prod := by
      rw [hx.2, pow_two]
      intro h
      exact hqm (Nat.dvd_of_mul_dvd_mul_right hq.pos h)
    have hfinS : {y : Multiset ℕ | IsNatFactorization (m * q) y ∧ IsFactorizationCoarsening x y ∧
        y.card < x.card}.Finite :=
      (setOf_isNatFactorization_finite _).subset (fun y hy => hy.1)
    have hfinC : {y : Multiset ℕ | IsFactorizationCoarsening x y}.Finite :=
      (setOf_isNatFactorization_finite (m * q)).subset (fun y hy => coars_fact hx hy)
    have h5 := factorization_coarsening_signed_orderings_sum_zero q hq x hx.1
      (by rw [hx.2]; exact dvd_mul_left q m) hsq (by omega)
    change ∑ᶠ y ∈ {y : Multiset ℕ | IsFactorizationCoarsening x y}, fw q y = 0 at h5
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinC] at h5
    have hC : hfinC.toFinset = insert x hfinS.toFinset := by
      ext y
      simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Set.mem_ofPred_eq]
      constructor
      · intro hy
        by_cases hyx : y = x
        · exact Or.inl hyx
        · exact Or.inr ⟨coars_fact hx hy, hy, (isFactorizationCoarsening_card_lt_iff_ne hy).2 hyx⟩
      · rintro (rfl | hy)
        · exact isFactorizationCoarsening_refl _
        · exact hy.2.1
    have hxS : x ∉ hfinS.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro h; exact lt_irrefl _ h.2.2
    rw [hC, Finset.sum_insert hxS] at h5
    change ((-∑ᶠ y ∈ {y : Multiset ℕ | IsNatFactorization (m * q) y ∧ IsFactorizationCoarsening x y ∧
        y.card < x.card}, factorizationMobiusToTop (m * q) y : ℤ) : ℚ) = fw q x
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinS]
    push_cast
    rw [Finset.sum_congr rfl (fun y hy => by
      have hy' := (Set.Finite.mem_toFinset _).1 hy
      exact ih y.card (hk ▸ hy'.2.2) y hy'.1 rfl)]
    linarith

end FactMobT1

theorem factorization_mobius_simple_prime
    (m q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m) (x : Multiset ℕ)
    (hx : IsNatFactorization (m * q) x) :
    (factorizationMobiusToTop (m * q) x : ℚ) =
      ((-1 : ℚ) ^ (x.card - 1) * ((x.card - 1).factorial : ℚ) /
        ∏ a ∈ (x.filter (fun a => ¬ q ∣ a)).toFinset,
          (((x.filter (fun a => ¬ q ∣ a)).count a).factorial : ℚ)) := by
  exact FactMobT1.thm1 m q hq hqm x hx
