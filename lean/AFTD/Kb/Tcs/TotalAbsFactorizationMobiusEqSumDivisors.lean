import AFTD.Prelude
import AFTD.Kb.Tcs.TotalAbsFactorizationMobius
import AFTD.Kb.Tcs.FactorizationMobiusSimplePrime
import AFTD.Kb.Tcs.OrderedFactorizationCount
import AFTD.Kb.Tcs.SetOfIsNatFactorizationFinite
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.FactorizationMobiusToTop
import AFTD.Kb.Tcs.IsNatFactorization

/-!
# total_abs_factorization_mobius_eq_sum_divisors

Topic: combinatorics   Node: 91bf7393ddd6

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), proof of Corollary 7 (first step)

If q is a prime not dividing m ≥ 1, then a(mq) = Σ_{d | m} H(m/d).
-/

namespace TAFM

noncomputable def P (z : Multiset ℕ) : ℚ := ∏ a ∈ z.toFinset, ((z.count a).factorial : ℚ)

lemma P_pos (z : Multiset ℕ) : 0 < P z :=
  Finset.prod_pos (fun a _ => by exact_mod_cast Nat.factorial_pos _)

lemma P_cons (v : ℕ) (z : Multiset ℕ) : P (v ::ₘ z) = ((z.count v + 1 : ℕ) : ℚ) * P z := by
  unfold P
  have hsub : z.toFinset ⊆ (v ::ₘ z).toFinset := by
    intro a ha; simp only [Multiset.mem_toFinset] at ha ⊢; exact Multiset.mem_cons_of_mem ha
  rw [Finset.prod_subset (f := fun a => ((z.count a).factorial : ℚ)) hsub (fun a _ ha => by
    rw [Multiset.count_eq_zero.2 (fun h => ha (Multiset.mem_toFinset.2 h))]; simp)]
  have hv : v ∈ (v ::ₘ z).toFinset := by simp
  rw [← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ (fun a => ((z.count a).factorial : ℚ)) hv]
  rw [Multiset.count_cons_self, Nat.factorial_succ]
  rw [Finset.prod_congr rfl (fun a ha => by
    have : a ≠ v := Finset.ne_of_mem_erase ha
    rw [Multiset.count_cons_of_ne this])]
  push_cast; ring

lemma P_erase {v : ℕ} {z : Multiset ℕ} (hv : v ∈ z) : P z = ((z.count v : ℕ) : ℚ) * P (z.erase v) := by
  have h := P_cons v (z.erase v)
  rw [Multiset.cons_erase hv] at h
  rw [h]
  congr 2
  rw [← Multiset.count_cons_self v (z.erase v), Multiset.cons_erase hv]

/-- the distinct orderings of a multiset -/
noncomputable def S (M : Multiset ℕ) : Finset (List ℕ) := M.toList.permutations.toFinset

lemma mem_S {M : Multiset ℕ} {l : List ℕ} : l ∈ S M ↔ (l : Multiset ℕ) = M := by
  unfold S
  rw [List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h; rw [← Multiset.coe_toList M]; exact Multiset.coe_eq_coe.2 h
  · intro h; subst h; exact Multiset.coe_eq_coe.1 (by simp)

lemma S_card (M : Multiset ℕ) : ((S M).card : ℚ) = (M.card.factorial : ℚ) / P M := by
  induction h : M.card using Nat.strong_induction_on generalizing M with
  | _ k ih =>
  by_cases hM : M = 0
  · subst hM
    have : S 0 = {[]} := by
      ext l; rw [mem_S, Finset.mem_singleton]; simp
    rw [this]; simp at h; subst h; simp [P]
  · have hS : S M = M.toFinset.biUnion (fun a => (S (M.erase a)).image (List.cons a)) := by
      ext l
      simp only [mem_S, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]
      constructor
      · intro hl
        cases l with
        | nil => exact absurd hl.symm (by simpa using hM)
        | cons a l' =>
          refine ⟨a, ?_, l', ?_, rfl⟩
          · rw [← hl]; simp
          · rw [← hl]; simp
      · rintro ⟨a, ha, l', hl', rfl⟩
        rw [← Multiset.cons_coe, hl', Multiset.cons_erase ha]
    rw [hS, Finset.card_biUnion]
    · push_cast
      rw [Finset.sum_congr rfl (fun a ha => by
        rw [Finset.card_image_of_injective _ (List.cons_injective)])]
      have hk : ∀ a ∈ M.toFinset, (M.erase a).card = k - 1 := by
        intro a ha; rw [Multiset.card_erase_of_mem (Multiset.mem_toFinset.1 ha), h]; rfl
      rw [Finset.sum_congr rfl (fun a ha => ih (k - 1) (by
        have := Multiset.card_pos.2 hM; omega) (M.erase a) (hk a ha))]
      have key : ∀ a ∈ M.toFinset, ((k - 1).factorial : ℚ) / P (M.erase a)
          = ((k - 1).factorial : ℚ) * ((M.count a : ℕ) : ℚ) / P M := by
        intro a ha
        have ha' := Multiset.mem_toFinset.1 ha
        have hc : ((M.count a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Multiset.count_pos.2 ha').ne'
        have := P_pos (M.erase a)
        rw [P_erase ha']
        field_simp
      rw [Finset.sum_congr rfl key, ← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum,
        Multiset.toFinset_sum_count_eq, h]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := Multiset.card_pos.2 hM; omega⟩
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast; ring
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro l hla hlb
      simp only [Finset.mem_image] at hla hlb
      obtain ⟨_, _, rfl⟩ := hla
      obtain ⟨_, _, h2⟩ := hlb
      exact hab (List.cons.inj h2).1.symm

lemma H_eq (n : ℕ) : orderedFactorizationCount n =
    ∑ M ∈ (setOf_isNatFactorization_finite n).toFinset, (S M).card := by
  set T := (setOf_isNatFactorization_finite n).toFinset.biUnion S with hT
  have hmemT : ∀ l, l ∈ T ↔ ((∀ a ∈ l, 1 < a) ∧ l.prod = n) := by
    intro l
    rw [hT, Finset.mem_biUnion]
    constructor
    · rintro ⟨M, hM, hl⟩
      rw [Set.Finite.mem_toFinset] at hM
      rw [mem_S] at hl; subst hl
      exact ⟨fun a ha => hM.1 a (Multiset.mem_coe.2 ha), by simpa using hM.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(l : Multiset ℕ), ?_, mem_S.2 rfl⟩
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun a ha => h1 a (Multiset.mem_coe.1 ha), by simpa using h2⟩
  unfold orderedFactorizationCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun l => (hmemT l).symm)), Nat.card_eq_fintype_card,
    Fintype.card_coe, hT, Finset.card_biUnion]
  intro M _ M' _ hMM'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro l h1 h2
  rw [mem_S] at h1 h2
  exact hMM' (h1.symm.trans h2)

lemma split_marked {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m) {x : Multiset ℕ}
    (hx : IsNatFactorization (m * q) x) :
    ∃ t U, x = t ::ₘ U ∧ q ∣ t ∧ ∀ b ∈ U, ¬ q ∣ b := by
  have hd : q ∣ x.prod := by rw [hx.2]; exact dvd_mul_left q m
  obtain ⟨t, ht, hqt⟩ := hq.prime.exists_mem_multiset_dvd hd
  refine ⟨t, x.erase t, (Multiset.cons_erase ht).symm, hqt, fun b hb hqb => hqm ?_⟩
  have h1 : q * q ∣ x.prod := by
    rw [← Multiset.cons_erase ht, Multiset.prod_cons]
    exact mul_dvd_mul hqt (hqb.trans (Multiset.dvd_prod hb))
  rw [hx.2] at h1
  exact Nat.dvd_of_mul_dvd_mul_right hq.pos h1

lemma abs_mu {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m) {x : Multiset ℕ}
    (hx : IsNatFactorization (m * q) x) :
    (factorizationMobiusToTop (m * q) x).natAbs = (S (x.filter (fun a => ¬ q ∣ a))).card := by
  have h := factorization_mobius_simple_prime m q hq hqm x hx
  obtain ⟨t, U, rfl, hqt, hU⟩ := split_marked hq hqm hx
  have hf : (t ::ₘ U).filter (fun a => ¬ q ∣ a) = U := by
    rw [Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 hqt), Multiset.filter_eq_self.2 hU]
  rw [hf] at h ⊢
  rw [Multiset.card_cons, Nat.add_sub_cancel] at h
  have h' : (factorizationMobiusToTop (m * q) (t ::ₘ U) : ℚ) = (-1 : ℚ) ^ U.card * (U.card.factorial : ℚ) / P U := h
  have hc := S_card U
  have : (((factorizationMobiusToTop (m * q) (t ::ₘ U)).natAbs : ℕ) : ℚ) = ((S U).card : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, h', hc, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_pos (P_pos U), abs_of_nonneg (by positivity)]
  exact_mod_cast this

theorem main (m q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m) (hm : 0 < m) :
    totalAbsFactorizationMobius (m * q) = ∑ d ∈ m.divisors, orderedFactorizationCount (m / d) := by
  have hfin := setOf_isNatFactorization_finite (m * q)
  unfold totalAbsFactorizationMobius
  change ∑ᶠ x ∈ {x : Multiset ℕ | IsNatFactorization (m * q) x}, (factorizationMobiusToTop (m * q) x).natAbs = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl (fun x hx => abs_mu hq hqm (hfin.mem_toFinset.1 hx))]
  simp only [H_eq]
  rw [← Finset.sum_sigma (s := m.divisors) (t := fun d => (setOf_isNatFactorization_finite (m / d)).toFinset)
    (f := fun p : (Σ _ : ℕ, Multiset ℕ) => (S p.2).card)]
  have hq2 := hq.two_le
  apply Finset.sum_nbij' (fun x => (⟨(x.filter (fun a => q ∣ a)).prod / q, x.filter (fun a => ¬ q ∣ a)⟩ : Σ _ : ℕ, Multiset ℕ))
    (fun p => (q * p.1) ::ₘ p.2)
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨t, U, rfl, hqt, hU⟩ := split_marked hq hqm hx
    rw [Finset.mem_sigma, Set.Finite.mem_toFinset, Nat.mem_divisors]
    rw [Multiset.filter_cons_of_pos (p := fun a => q ∣ a) _ hqt, Multiset.filter_eq_nil.2 hU,
      Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 hqt), Multiset.filter_eq_self.2 hU]
    obtain ⟨d, rfl⟩ := hqt
    simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
    rw [Nat.mul_div_cancel_left _ hq.pos]
    have hprod := hx.2
    rw [Multiset.prod_cons] at hprod
    have hdU : d * U.prod = m := by
      have : q * (d * U.prod) = q * m := by rw [← mul_assoc, hprod, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hq.pos this
    refine ⟨⟨⟨U.prod, hdU.symm⟩, hm.ne'⟩, fun a ha => hx.1 a (Multiset.mem_cons_of_mem ha), ?_⟩
    rw [← hdU]
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hdU; omega
      · exact h
    rw [Nat.mul_div_cancel_left _ hd0]
  · rintro ⟨d, M⟩ hp
    rw [Finset.mem_sigma, Set.Finite.mem_toFinset, Nat.mem_divisors] at hp
    obtain ⟨⟨hdm, _⟩, hM⟩ := hp
    rw [Set.Finite.mem_toFinset]
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 ha with rfl | ha
      · nlinarith
      · exact hM.1 a ha
    · rw [Multiset.prod_cons, hM.2, mul_assoc, Nat.mul_div_cancel' hdm, mul_comm]
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨t, U, rfl, hqt, hU⟩ := split_marked hq hqm hx
    dsimp only
    rw [Multiset.filter_cons_of_pos (p := fun a => q ∣ a) _ hqt, Multiset.filter_eq_nil.2 hU,
      Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 hqt), Multiset.filter_eq_self.2 hU]
    simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
    rw [Nat.mul_div_cancel' hqt]
  · rintro ⟨d, M⟩ hp
    rw [Finset.mem_sigma, Set.Finite.mem_toFinset, Nat.mem_divisors] at hp
    obtain ⟨⟨hdm, _⟩, hM⟩ := hp
    have hMq : ∀ b ∈ M, ¬ q ∣ b := by
      intro b hb hqb
      apply hqm
      have h1 : b ∣ m / d := hM.2 ▸ Multiset.dvd_prod hb
      exact hqb.trans (h1.trans (Nat.div_dvd_of_dvd hdm))
    have hqd : q ∣ q * d := dvd_mul_right q d
    dsimp only
    rw [Multiset.filter_cons_of_pos (p := fun a => q ∣ a) _ hqd, Multiset.filter_eq_nil.2 hMq,
      Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 hqd), Multiset.filter_eq_self.2 hMq]
    simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
    rw [Nat.mul_div_cancel_left _ hq.pos]
  · intro x hx
    rfl

end TAFM

theorem total_abs_factorization_mobius_eq_sum_divisors
    (m q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m) (hm : 0 < m) :
    totalAbsFactorizationMobius (m * q) = ∑ d ∈ m.divisors, orderedFactorizationCount (m / d) := by
  exact TAFM.main m q hq hqm hm
