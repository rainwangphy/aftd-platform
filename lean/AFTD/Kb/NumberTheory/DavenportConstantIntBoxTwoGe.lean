import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportConstant
import AFTD.Kb.NumberTheory.IntBoxTwo
import AFTD.Kb.NumberTheory.NatLeastPrimeNotDvd
import AFTD.Kb.NumberTheory.DavenportBoxExtremalSequence
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum
import AFTD.Kb.NumberTheory.IntBoxExtremalSequenceCounts
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# davenport_constant_int_box_two_ge

Topic: elementary_number_theory   Node: 96d8dcaf00e0

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Corollary 2 (via Theorem 1's sequence S(m)); the proof here checks minimality of S(m) directly.

For every m ≥ 2, the Davenport constant of the box ⟦−m, m⟧² is at least 4m² − q(m), q(m) the smallest prime not dividing m: S(m) is a minimal zero-sum sequence of that length.
-/

theorem davenport_constant_int_box_two_ge (m : ℕ) (hm : 2 ≤ m) :
    ((4 * m ^ 2 - nat_least_prime_not_dvd m : ℕ) : ℕ∞) ≤
      davenport_constant (↑(int_box_two m) : Set (ℤ × ℤ)) := by
  set q := nat_least_prime_not_dvd m with hqdef
  -- the smallest prime not dividing `m`
  have hne : {p | p.Prime ∧ ¬ p ∣ m}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (m + 1)
    exact ⟨p, hp2, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩
  have hq : q.Prime ∧ ¬ q ∣ m := Nat.sInf_mem hne
  have hqmin : ∀ p, p.Prime → ¬ p ∣ m → q ≤ p := fun p hp hpd => Nat.sInf_le ⟨hp, hpd⟩
  have hq2 : 2 ≤ q := hq.1.two_le
  have hqle : q ≤ 2 * m := by
    obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
    exact (hqmin p hp (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).trans hp2m
  have hqne : q ≠ 2 * m := by
    intro h
    have := hq.1
    rw [h, Nat.prime_mul_iff] at this
    rcases this with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  have hsmall : ∀ p, p.Prime → p < q → p ∣ m := by
    intro p hp hpq
    by_contra hpd
    exact absurd (hqmin p hp hpd) (by omega)
  have hcop1 : Nat.Coprime (2 * m - 1) (q - 1) := by
    apply Nat.coprime_of_dvd
    intro p hp h1 h2
    have hpq : p < q := by
      have := Nat.le_of_dvd (by omega) h2
      omega
    have hpm := hsmall p hp hpq
    have : p ∣ 2 * m - (2 * m - 1) := Nat.dvd_sub (dvd_mul_of_dvd_right hpm 2) h1
    rw [show 2 * m - (2 * m - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hcopqm : Nat.Coprime q m := (Nat.Prime.coprime_iff_not_dvd hq.1).2 hq.2
  -- integer versions
  set M : ℤ := (m : ℤ) with hM
  set Q : ℤ := (q : ℤ) with hQ
  have hM2 : 2 ≤ M := by rw [hM]; exact_mod_cast hm
  have hQ2 : 2 ≤ Q := by rw [hQ]; exact_mod_cast hq2
  have hQle : Q < 2 * M := by rw [hM, hQ]; exact_mod_cast (lt_of_le_of_ne hqle hqne)
  have hcopZ : IsCoprime (2 * M - 1) (2 * M - Q) := by
    have h1 : IsCoprime ((2 * m - 1 : ℕ) : ℤ) ((q - 1 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hcop1
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_sub (show 1 ≤ q by omega)] at h1
    have : 2 * M - Q = (2 * M - 1) + (-1) * (Q - 1) := by ring
    rw [this]
    exact (h1.neg_right.mul_add_left_right 1).symm.symm |> fun h => by
      simpa [add_comm, mul_comm] using (IsCoprime.add_mul_left_right h1.neg_right 1)
  have hcopMQ : IsCoprime M Q := by
    rw [hM, hQ]; exact Nat.isCoprime_iff_coprime.2 hcopqm.symm
  set v₁ : ℤ × ℤ := (M, M) with hv₁
  set v₂ : ℤ × ℤ := (-M, M - 1) with hv₂
  set v₃ : ℤ × ℤ := (M - Q, -M) with hv₃
  set k₁ := q * (m - 1) + m with hk₁
  set k₂ := 2 * m ^ 2 - m * q with hk₂
  set k₃ := 2 * m ^ 2 - m with hk₃
  have hk₁Z : (k₁ : ℤ) = Q * (M - 1) + M := by
    rw [hk₁]; push_cast [Nat.cast_sub (show 1 ≤ m by omega)]; ring
  have hk₂Z : (k₂ : ℤ) = M * (2 * M - Q) := by
    rw [hk₂]
    have : m * q ≤ 2 * m ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hk₃Z : (k₃ : ℤ) = M * (2 * M - 1) := by
    rw [hk₃]
    have : m ≤ 2 * m ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hS : davenport_box_extremal_sequence m =
      Multiset.replicate k₁ v₁ + Multiset.replicate k₂ v₂ + Multiset.replicate k₃ v₃ := rfl
  have h12 : v₁ ≠ v₂ := by
    intro h; have := congrArg Prod.fst h; simp only [hv₁, hv₂] at this; omega
  have h13 : v₁ ≠ v₃ := by
    intro h; have := congrArg Prod.snd h; simp only [hv₁, hv₃] at this; omega
  have h23 : v₂ ≠ v₃ := by
    intro h; have := congrArg Prod.snd h; simp only [hv₂, hv₃] at this; omega
  have hsum3 : ∀ a b c : ℕ, (Multiset.replicate a v₁ + Multiset.replicate b v₂ +
      Multiset.replicate c v₃).sum = ((a : ℤ) * M - b * M + c * (M - Q),
        (a : ℤ) * M + b * (M - 1) - c * M) := by
    intro a b c
    simp only [Multiset.sum_add, Multiset.sum_replicate, hv₁, hv₂, hv₃, Prod.smul_mk,
      Prod.mk_add_mk, nsmul_eq_mul]
    ext <;> simp <;> ring
  have hcount : ∀ (a b c : ℕ) (x : ℤ × ℤ), (Multiset.replicate a v₁ + Multiset.replicate b v₂ +
      Multiset.replicate c v₃).count x =
      (if x = v₁ then a else 0) + (if x = v₂ then b else 0) + (if x = v₃ then c else 0) := by
    intro a b c x
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_replicate,
      Multiset.count_replicate, Multiset.count_replicate]
    simp only [@eq_comm _ v₁ x, @eq_comm _ v₂ x, @eq_comm _ v₃ x]
  have hmin : multiset_is_minimal_zero_sum (davenport_box_extremal_sequence m) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hS]
      intro h
      have := congrArg Multiset.card h
      simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_zero] at this
      omega
    · rw [hS, hsum3, hk₁Z, hk₂Z, hk₃Z]
      ext <;> simp <;> ring
    · intro t ht ht0 hts
      rw [hS] at ht ⊢
      set a := t.count v₁
      set b := t.count v₂
      set c := t.count v₃
      have hteq : t = Multiset.replicate a v₁ + Multiset.replicate b v₂ +
          Multiset.replicate c v₃ := by
        ext x
        rw [hcount]
        by_cases h1 : x = v₁
        · rw [h1, if_pos rfl, if_neg h12, if_neg h13]
          simp only [add_zero]
          rfl
        by_cases h2 : x = v₂
        · rw [h2, if_neg h12.symm, if_pos rfl, if_neg h23]
          simp only [zero_add, add_zero]
          rfl
        by_cases h3 : x = v₃
        · rw [h3, if_neg h13.symm, if_neg h23.symm, if_pos rfl]
          simp only [zero_add]
          rfl
        simp only [h1, h2, h3, if_false, add_zero]
        rw [Multiset.count_eq_zero]
        intro hx
        have := Multiset.mem_of_le ht hx
        simp only [Multiset.mem_add, Multiset.mem_replicate] at this
        tauto
      have ha : a ≤ k₁ := by
        have := Multiset.count_le_of_le v₁ ht
        rwa [hcount, if_pos rfl, if_neg h12, if_neg h13, add_zero, add_zero] at this
      have hb : b ≤ k₂ := by
        have := Multiset.count_le_of_le v₂ ht
        rwa [hcount, if_neg h12.symm, if_pos rfl, if_neg h23, zero_add, add_zero] at this
      have hc : c ≤ k₃ := by
        have := Multiset.count_le_of_le v₃ ht
        rwa [hcount, if_neg h13.symm, if_neg h23.symm, if_pos rfl, zero_add, zero_add] at this
      rw [hteq, hsum3] at hts
      have ex := congrArg Prod.fst hts
      have ey := congrArg Prod.snd hts
      simp only [Prod.fst_zero, Prod.snd_zero] at ex ey
      set A : ℤ := (a : ℤ) with hAd
      set B : ℤ := (b : ℤ) with hBd
      set C : ℤ := (c : ℤ) with hCd
      have hA0 : 0 ≤ A := Nat.cast_nonneg _
      have hB0 : 0 ≤ B := Nat.cast_nonneg _
      have hC0 : 0 ≤ C := Nat.cast_nonneg _
      have hCle : C ≤ M * (2 * M - 1) := by rw [← hk₃Z, hCd]; exact_mod_cast hc
      rcases int_box_extremal_sequence_counts M Q A B C hM2 hcopMQ hcopZ hC0 hCle
          (by linear_combination ex) (by linear_combination ey) with
        ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
      · exfalso
        have ha0 : a = 0 := by rw [hAd] at hA; exact_mod_cast hA
        have hb0 : b = 0 := by rw [hBd] at hB; exact_mod_cast hB
        have hc0 : c = 0 := by rw [hCd] at hC; exact_mod_cast hC
        apply ht0
        rw [hteq, ha0, hb0, hc0]
        simp
      · have ha1 : a = k₁ := by
          have : A = (k₁ : ℤ) := by rw [hA, hk₁Z]
          rw [hAd] at this
          exact_mod_cast this
        have hb1 : b = k₂ := by
          have : B = (k₂ : ℤ) := by rw [hB, hk₂Z]
          rw [hBd] at this
          exact_mod_cast this
        have hc1 : c = k₃ := by
          have : C = (k₃ : ℤ) := by rw [hC, hk₃Z]
          rw [hCd] at this
          exact_mod_cast this
        rw [hteq, ha1, hb1, hc1]
  have hbox : ∀ x ∈ davenport_box_extremal_sequence m, x ∈ int_box_two m := by
    intro x hx
    rw [hS] at hx
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
    simp only [int_box_two, Finset.mem_product, Finset.mem_Icc]
    rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;>
      simp only [hv₁, hv₂, hv₃] <;> constructor <;> constructor <;> omega
  have hcard : Multiset.card (davenport_box_extremal_sequence m) = 4 * m ^ 2 - q := by
    rw [hS]
    simp only [Multiset.card_add, Multiset.card_replicate]
    have h1 : ((k₁ + k₂ + k₃ : ℕ) : ℤ) = ((4 * m ^ 2 - q : ℕ) : ℤ) := by
      have : q ≤ 4 * m ^ 2 := by nlinarith
      push_cast [Nat.cast_sub this]
      rw [hk₁Z, hk₂Z, hk₃Z]
      ring
    exact_mod_cast h1
  unfold davenport_constant
  apply le_sSup
  exact ⟨_, fun x hx => hbox x hx, hmin, by rw [hcard]⟩
