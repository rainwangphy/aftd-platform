import AFTD.Prelude

/-!
# order_rigidity_arithmetic_consequences

Topic: information   Node: 86459f3d8d9f

Provenance: formalization of a published result. Source: arXiv:2610.28047 Theorem 3.1

If 2 <= k <= n - 2 and ord_d(q) = k for every divisor d > 1 of n, then every prime l dividing n satisfies ord_l(q) = k and k | (l - 1), n is odd, gcd(n, q-1) = gcd(n, k) = 1, and n = mk + 1 for some integer m >= 2.
-/

lemma order_rigidity_arithmetic_consequences.k_dvd_sub_one_of_forall_prime_dvd (k : ℕ) :
    ∀ N : ℕ, (∀ p, Nat.Prime p → p ∣ N → k ∣ p - 1) → k ∣ N - 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hpos.ne') with h1 | hgt
    · rw [← h1]; simp
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgt.ne'
      have hpn : p ≤ N := Nat.le_of_dvd hpos hpdvd
      have hm1 : 1 ≤ N / p := Nat.div_pos hpn hp.pos
      have hmlt : N / p < N := Nat.div_lt_self hpos hp.one_lt
      have hmdvd : N / p ∣ N := Nat.div_dvd_of_dvd hpdvd
      have hk1 : k ∣ N / p - 1 := ih (N / p) hmlt (fun r hr hrd => h r hr (dvd_trans hrd hmdvd))
      have hk2 : k ∣ p - 1 := h p hp hpdvd
      have ha : 1 ≡ N / p [MOD k] := (Nat.modEq_iff_dvd' hm1).mpr hk1
      have hb : 1 ≡ p [MOD k] := (Nat.modEq_iff_dvd' hp.one_lt.le).mpr hk2
      have hab : 1 ≡ N / p * p [MOD k] := by simpa using ha.mul hb
      have hprod : 1 ≤ N / p * p := by
        have := Nat.mul_pos (by omega : 0 < N / p) hp.pos
        omega
      have hres : k ∣ N / p * p - 1 := (Nat.modEq_iff_dvd' hprod).mp hab
      rwa [Nat.div_mul_cancel hpdvd] at hres

/-- Arithmetic consequences of the divisor order rigidity condition. -/
theorem order_rigidity_arithmetic_consequences (q n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 2) (hord : ∀ d : ℕ, d ∣ n → 1 < d → orderOf (q : ZMod d) = k) : (∀ l : ℕ, Nat.Prime l → l ∣ n → orderOf (q : ZMod l) = k ∧ k ∣ l - 1) ∧ Odd n ∧ Nat.gcd n (q - 1) = 1 ∧ Nat.gcd n k = 1 ∧ ∃ m ≥ 2, n = m * k + 1 := by
  have hn4 : 4 ≤ n := by omega
  have hn1 : 1 < n := by omega
  have hnpos : 0 < n := by omega
  have hprime : ∀ l : ℕ, Nat.Prime l → l ∣ n → orderOf (q : ZMod l) = k ∧ k ∣ l - 1 := by
    intro l hl hldvd
    have hordl : orderOf (q : ZMod l) = k := hord l hldvd hl.one_lt
    refine ⟨hordl, ?_⟩
    have : Fact l.Prime := ⟨hl⟩
    have hne : (q : ZMod l) ≠ 0 := by
      intro hzero
      rw [hzero] at hordl
      simp at hordl
      omega
    have hdvd := ZMod.orderOf_dvd_card_sub_one hne
    rwa [hordl] at hdvd
  obtain ⟨p0, hp0, hp0dvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hq0 : q ≠ 0 := by
    have : Fact p0.Prime := ⟨hp0⟩
    intro hq
    have h := (hprime p0 hp0 hp0dvd).1
    rw [hq] at h
    simp at h
    omega
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  refine ⟨hprime, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.not_even_iff_odd]
    intro heven
    have h2 : 2 ∣ n := even_iff_two_dvd.mp heven
    have hkk := (hprime 2 Nat.prime_two h2).2
    simp at hkk
    omega
  · by_contra hg
    have hgt : 1 < Nat.gcd n (q - 1) := by
      have h1 : 0 < Nat.gcd n (q - 1) := Nat.gcd_pos_of_pos_left (q - 1) hnpos
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgt.ne'
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left n (q - 1))
    have hpq : p ∣ q - 1 := dvd_trans hpdvd (Nat.gcd_dvd_right n (q - 1))
    have hordp : orderOf (q : ZMod p) = k := (hprime p hp hpn).1
    have : Fact p.Prime := ⟨hp⟩
    have hqmod : (q : ZMod p) = 1 := by
      have hzero : ((q - 1 : ℕ) : ZMod p) = 0 := by
        rw [CharP.cast_eq_zero_iff (ZMod p) p]
        exact hpq
      calc (q : ZMod p) = ((q - 1 : ℕ) : ZMod p) + 1 := by
              rw [Nat.cast_sub hq1, Nat.cast_one]; ring
        _ = 1 := by rw [hzero, zero_add]
    rw [hqmod, orderOf_one] at hordp
    omega
  · by_contra hg
    have hgt : 1 < Nat.gcd n k := by
      have h1 : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k hnpos
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgt.ne'
    have hp2 : 2 ≤ p := hp.two_le
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left n k)
    have hpk : p ∣ k := dvd_trans hpdvd (Nat.gcd_dvd_right n k)
    have hkp : k ∣ p - 1 := (hprime p hp hpn).2
    have hpp : p ∣ p - 1 := dvd_trans hpk hkp
    have h1 : p ∣ 1 := by
      have h := Nat.dvd_sub (dvd_refl p) hpp
      rwa [Nat.sub_sub_self hp.one_le] at h
    rw [Nat.dvd_one] at h1
    omega
  · have hkdiv : k ∣ n - 1 :=
      order_rigidity_arithmetic_consequences.k_dvd_sub_one_of_forall_prime_dvd k n (fun p hp hpd => (hprime p hp hpd).2)
    obtain ⟨m, hm⟩ := hkdiv
    have hm' : n - 1 = m * k := by rw [hm, Nat.mul_comm]
    refine ⟨m, ?_, ?_⟩
    · have hkey : k * 1 < k * m := by
        rw [mul_one, Nat.mul_comm k m, ← hm']
        omega
      have := Nat.lt_of_mul_lt_mul_left hkey
      omega
    · omega
