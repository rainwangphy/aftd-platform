import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber
import AFTD.Kb.NumberTheory.IsStronglyMatchable
import AFTD.Kb.NumberTheory.FinCardFilterDvd

/-!
# is_m_number_of_strongly_matchable

Topic: elementary_number_theory   Node: 501481a90e1b

Provenance: helper lemma. arXiv:2610.37512 Section 3

If a positive integer n is strongly matchable, then n is an M-number.
-/

lemma is_m_number_of_strongly_matchable_aux_div_lt_div_ceil (N p : ℕ) (hN : 0 < N) (hp : 2 ≤ p) :
    N / (p + 1) < (N + p - 1) / p := by
  have H : (p + 1) * (N / (p + 1)) ≤ N := Nat.mul_div_le N (p + 1)
  have H2 : p * (N / (p + 1)) + (N / (p + 1)) ≤ N := by
    calc p * (N / (p + 1)) + (N / (p + 1)) = (p + 1) * (N / (p + 1)) := by ring
    _ ≤ N := H
  by_cases h0 : N / (p + 1) = 0
  · rw [h0]
    have : 0 < (N + p - 1) / p := by
      rw [Nat.div_pos_iff]
      omega
    omega
  · have h1 : 1 ≤ N / (p + 1) := Nat.pos_of_ne_zero h0
    have h2 : (N / (p + 1) + 1) * p ≤ N + p - 1 := by
      calc (N / (p + 1) + 1) * p = p * (N / (p + 1)) + p := by ring
      _ ≤ (N - 1) + p := by omega
      _ = N + p - 1 := by omega
    have h3 : N / (p + 1) + 1 ≤ (N + p - 1) / p := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      exact h2
    omega

lemma is_m_number_of_strongly_matchable_aux_card_le (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hpn : p ^ p ∣ n) :
    let D0 := n.divisors.filter (fun d => ¬ p ∣ d)
    (p + 1) * D0.card ≤ n.divisors.card := by
  intro D0
  have hp_pos : 0 < p := hp.pos
  have hp_pow (k : ℕ) : 0 < p ^ k := pow_pos hp_pos k
  have H (k1 k2 d1 d2 : ℕ) (hpd1 : ¬ p ∣ d1) (hpd2 : ¬ p ∣ d2)
      (heq : p ^ k1 * d1 = p ^ k2 * d2) (hle : k1 ≤ k2) : k1 = k2 ∧ d1 = d2 := by
    rcases hle.eq_or_lt with rfl | hlt
    · have hd : d1 = d2 := Nat.eq_of_mul_eq_mul_left (hp_pow k1) heq
      exact ⟨rfl, hd⟩
    · obtain ⟨m, rfl⟩ : ∃ m, k2 = k1 + m + 1 := Nat.exists_eq_add_of_lt hlt
      have heq2 : d1 = p ^ (m + 1) * d2 := by
        apply Nat.eq_of_mul_eq_mul_left (hp_pow k1)
        calc p ^ k1 * d1 = p ^ (k1 + (m + 1)) * d2 := heq
        _ = (p ^ k1 * p ^ (m + 1)) * d2 := by rw [pow_add]
        _ = p ^ k1 * (p ^ (m + 1) * d2) := by rw [mul_assoc]
      have hdvd : p ∣ d1 := by
        rw [heq2]
        have : p ∣ p ^ (m + 1) := dvd_pow_self p (by omega)
        exact dvd_mul_of_dvd_left this d2
      exact (hpd1 hdvd).elim
  let S := (Finset.range (p + 1)) ×ˢ D0
  let f : ℕ × ℕ → ℕ := fun x => p ^ x.1 * x.2
  have hinj : Set.InjOn f (S : Set (ℕ × ℕ)) := by
    intro ⟨k1, d1⟩ hx ⟨k2, d2⟩ hy heq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hx hy
    have hpd1 : ¬ p ∣ d1 := hx.2.2
    have hpd2 : ¬ p ∣ d2 := hy.2.2
    have h_pair : k1 = k2 ∧ d1 = d2 := by
      by_cases hle : k1 ≤ k2
      · exact H k1 k2 d1 d2 hpd1 hpd2 heq hle
      · have hle' : k2 ≤ k1 := by omega
        have := H k2 k1 d2 d1 hpd2 hpd1 heq.symm hle'
        exact ⟨this.1.symm, this.2.symm⟩
    exact Prod.ext h_pair.1 h_pair.2
  have hmaps : Set.MapsTo f (S : Set (ℕ × ℕ)) (n.divisors : Set ℕ) := by
    intro ⟨k, d⟩ hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hx
    have hk : k ≤ p := by omega
    have hd_mem : d ∈ n.divisors := hx.2.1
    have hpd : ¬ p ∣ d := hx.2.2
    rw [Finset.mem_coe, Nat.mem_divisors]
    have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd_mem).1
    have hcp : Nat.Coprime (p ^ p) d := by
      apply Nat.Coprime.pow_left
      exact hp.coprime_iff_not_dvd.mpr hpd
    have hmul : p ^ p * d ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcp hpn hd_dvd
    have hpow : p ^ k ∣ p ^ p := Nat.pow_dvd_pow p hk
    have hdvd : p ^ k * d ∣ p ^ p * d := Nat.mul_dvd_mul_right hpow d
    exact ⟨hdvd.trans hmul, hn⟩
  have hcard_le := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard_le
  exact hcard_le

/-- Every strongly matchable positive integer is an M-number. -/
theorem is_m_number_of_strongly_matchable (n : ℕ) (hn : 0 < n) (hm : is_strongly_matchable n) :
    is_m_number n := by
  intro p hp hpn
  let N := n.divisors.card
  have hN : 0 < N := by
    have : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
    exact Finset.card_pos.mpr ⟨1, this⟩
  let D0 := n.divisors.filter (fun d => ¬ p ∣ d)
  obtain ⟨e, he⟩ := hm p 1 zero_lt_one (Nat.coprime_one_right p)
  have he_coprime : ∀ i : Fin N, Nat.Coprime (e i : ℕ) (p + (i : ℕ)) := by
    intro i
    have := he i
    rw [one_mul] at this
    exact this
  let s := Finset.univ.filter (fun j : Fin N => p ∣ (j : ℕ))
  let g : Fin N → ℕ := fun j => (e j : ℕ)
  have hmaps : Set.MapsTo g (s : Set (Fin N)) (D0 : Set ℕ) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj ⊢
    have h_dvd : p ∣ (j : ℕ) := hj.2
    have h_mem : (e j : ℕ) ∈ n.divisors := Subtype.mem (e j)
    refine ⟨h_mem, ?_⟩
    intro hp_dvd
    have h_p_dvd_add : p ∣ p + (j : ℕ) := dvd_add dvd_rfl h_dvd
    have h_cp := he_coprime j
    have h_dvd_gcd : p ∣ Nat.gcd (e j : ℕ) (p + (j : ℕ)) := dvd_gcd hp_dvd h_p_dvd_add
    rw [h_cp] at h_dvd_gcd
    exact hp.not_dvd_one h_dvd_gcd
  have hinj : Set.InjOn g (s : Set (Fin N)) := by
    intro j1 _ j2 _ heq
    dsimp [g] at heq
    have : e j1 = e j2 := Subtype.ext heq
    exact e.injective this
  have hs_le_D0 : s.card ≤ D0.card := Finset.card_le_card_of_injOn g hmaps hinj
  have hs_card : s.card = (N + p - 1) / p := fin_card_filter_dvd p N hp.pos
  rw [hs_card] at hs_le_D0
  have hD0_mul : (p + 1) * D0.card ≤ N := is_m_number_of_strongly_matchable_aux_card_le n p (by omega) hp hpn
  have hD0_le : D0.card ≤ N / (p + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    rw [mul_comm]
    exact hD0_mul
  have h_le : (N + p - 1) / p ≤ N / (p + 1) := hs_le_D0.trans hD0_le
  have h_lt : N / (p + 1) < (N + p - 1) / p :=
    is_m_number_of_strongly_matchable_aux_div_lt_div_ceil N p hN hp.two_le
  omega
