import AFTD.Prelude
import AFTD.Kb.NumberTheory.NatPrimePowerParts
import AFTD.Kb.NumberTheory.NatPrimePowerPartsOne
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Support

/-!
# perm_order_eq_prod_and_sum_prime_power_parts_le

Topic: elementary_number_theory   Node: 75d64e75e202

Provenance: formalization of a published result. Source: arXiv:2610.11098 (An improved lower bound for separating words by permutation automata), Lemma 2.3.

Let k ≥ 1. If q is the order of some permutation of k elements and S(q) is the set of maximal prime-power divisors of q, then q = ∏_{s∈S(q)} s and ∑_{s∈S(q)} s ≤ k.
-/

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_sum_union_le_nat (A B : Finset ℕ) :
    ∑ s ∈ A ∪ B, s ≤ ∑ s ∈ A, s + ∑ s ∈ B, s := by
  have := Finset.sum_union_inter (f := fun (x:ℕ) => x) (s₁ := A) (s₂ := B)
  omega

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_sum_union_le (A B S : Finset ℕ) (hsub : S ⊆ A ∪ B) :
    ∑ s ∈ S, s ≤ ∑ s ∈ A, s + ∑ s ∈ B, s := by
  have h1 : ∑ s ∈ S, s ≤ ∑ s ∈ A ∪ B, s := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have h2 : ∑ s ∈ A ∪ B, s ≤ ∑ s ∈ A, s + ∑ s ∈ B, s := perm_order_eq_prod_and_sum_prime_power_parts_le_sum_union_le_nat A B
  exact h1.trans h2

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_lcm_subset (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    nat_prime_power_parts (a.lcm b) ⊆ nat_prime_power_parts a ∪ nat_prime_power_parts b := by
  intro s hs
  unfold nat_prime_power_parts at hs ⊢
  rcases Finset.mem_image.mp hs with ⟨p, hp, rfl⟩
  rw [Nat.mem_primeFactors] at hp
  have hlcm_fact : (a.lcm b).factorization p = max (a.factorization p) (b.factorization p) := by
    have hf := Nat.factorization_lcm ha hb
    rw [hf]
    rfl
  rw [hlcm_fact]
  rcases le_total (b.factorization p) (a.factorization p) with hle | hle
  · rw [max_eq_left hle]
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨p, ?_, rfl⟩
    rw [Nat.mem_primeFactors]
    refine ⟨hp.1, ?_, ha⟩
    have hpos : 0 < (a.lcm b).factorization p := hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1
    rw [hlcm_fact, max_eq_left hle] at hpos
    exact Nat.dvd_of_factorization_pos hpos.ne'
  · rw [max_eq_right hle]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨p, ?_, rfl⟩
    rw [Nat.mem_primeFactors]
    refine ⟨hp.1, ?_, hb⟩
    have hpos : 0 < (a.lcm b).factorization p := hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1
    rw [hlcm_fact, max_eq_right hle] at hpos
    exact Nat.dvd_of_factorization_pos hpos.ne'

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_injOn (q : ℕ) :
    Set.InjOn (fun p => p ^ q.factorization p) q.primeFactors := by
  intro p hp p' hp' h
  dsimp at h
  simp only [Finset.mem_coe, Nat.mem_primeFactors] at hp hp'
  have ha : q.factorization p ≠ 0 := by
    have := hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1
    omega
  have hdvd : p ∣ p' ^ q.factorization p' := by
    rw [← h]
    exact dvd_pow_self p ha
  have hprime_dvd := hp.1.dvd_of_dvd_pow hdvd
  exact (hp'.1.eq_one_or_self_of_dvd p hprime_dvd).resolve_left hp.1.ne_one

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_prod (q : ℕ) (hq : q ≠ 0) :
    q = ∏ s ∈ nat_prime_power_parts q, s := by
  unfold nat_prime_power_parts
  rw [Finset.prod_image (perm_order_eq_prod_and_sum_prime_power_parts_le_injOn q)]
  exact Nat.prod_primeFactors_pow_factorization hq

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_two_le {q s : ℕ} (hs : s ∈ nat_prime_power_parts q) : 2 ≤ s := by
  unfold nat_prime_power_parts at hs
  rcases Finset.mem_image.mp hs with ⟨p, hp, rfl⟩
  rw [Nat.mem_primeFactors] at hp
  have hpos : 0 < q.factorization p := hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1
  have hp2 : 2 ≤ p := hp.1.two_le
  calc 2 ≤ p := hp2
  _ ≤ p ^ q.factorization p := Nat.le_self_pow hpos.ne' _

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_prod (s : Finset ℕ) (h : ∀ x ∈ s, 2 ≤ x) :
    ∑ x ∈ s, x ≤ ∏ x ∈ s, x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.prod_insert has]
    have ha : 2 ≤ a := h a (Finset.mem_insert_self a s)
    have hs : ∀ x ∈ s, 2 ≤ x := fun x hx => h x (Finset.mem_insert_of_mem hx)
    have ih' := ih hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hprod : 2 ≤ ∏ x ∈ s, x := by
        obtain ⟨y, hy⟩ := hne
        have hy2 : 2 ≤ y := hs y hy
        have hdiv : y ∣ ∏ x ∈ s, x := Finset.dvd_prod_of_mem (fun x => x) hy
        have hpos : 0 < ∏ x ∈ s, x := by
          apply Finset.prod_pos
          intro x hx
          have := hs x hx
          omega
        exact Nat.le_of_dvd hpos hdiv |>.trans' hy2
      nlinarith

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_self (c : ℕ) (hc : c ≠ 0) :
    ∑ s ∈ nat_prime_power_parts c, s ≤ c := by
  have := perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_prod (nat_prime_power_parts c)
    (fun _ hx => perm_order_eq_prod_and_sum_prime_power_parts_le_two_le hx)
  rw [← perm_order_eq_prod_and_sum_prime_power_parts_le_prod c hc] at this
  exact this

lemma perm_order_eq_prod_and_sum_prime_power_parts_le_support {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) :
    ∑ s ∈ nat_prime_power_parts (orderOf σ), s ≤ σ.support.card := by
  refine Equiv.Perm.cycle_induction_on
    (fun σ => ∑ s ∈ nat_prime_power_parts (orderOf σ), s ≤ σ.support.card) σ ?_ ?_ ?_
  · rw [orderOf_one, nat_prime_power_parts_one, Finset.sum_empty, Equiv.Perm.support_one, Finset.card_empty]
  · intro τ hτ
    have hord : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
    have := perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_self (orderOf τ) hord
    rw [← hτ.orderOf]
    exact this
  · intro τ π hd hτ ihτ ihπ
    have hτ_pos : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
    have hπ_pos : orderOf π ≠ 0 := (orderOf_pos π).ne'
    rw [hd.orderOf]
    have hsub := perm_order_eq_prod_and_sum_prime_power_parts_le_lcm_subset (orderOf τ) (orderOf π) hτ_pos hπ_pos
    have hsum := perm_order_eq_prod_and_sum_prime_power_parts_le_sum_le_sum_union_le _ _ _ hsub
    have hsupp : (τ * π).support.card = τ.support.card + π.support.card := by
      rw [hd.support_mul, Finset.card_union_of_disjoint hd.disjoint_support]
    rw [hsupp]
    omega

theorem perm_order_eq_prod_and_sum_prime_power_parts_le (k : ℕ) (hk : 1 ≤ k) (q : ℕ)
    (hq : ∃ σ : Equiv.Perm (Fin k), orderOf σ = q) :
    q = ∏ s ∈ nat_prime_power_parts q, s ∧ ∑ s ∈ nat_prime_power_parts q, s ≤ k := by
  rcases hq with ⟨σ, rfl⟩
  have hq0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  refine ⟨perm_order_eq_prod_and_sum_prime_power_parts_le_prod (orderOf σ) hq0, ?_⟩
  have hle := perm_order_eq_prod_and_sum_prime_power_parts_le_support σ
  have hcard : σ.support.card ≤ k := by
    have := σ.support.card_le_univ
    rwa [Fintype.card_fin] at this
  exact hle.trans hcard
