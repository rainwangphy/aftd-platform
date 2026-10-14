import AFTD.Prelude

/-!
# layered_capacity_geometric_inequality

Topic: fair_division   Node: 12903d6e430d

Provenance: formalization of a published result. Source: arXiv:2610.15520 (Improving the bounds on approximating weighted maximin shares of chores), Lemma 5.3; the proof here uses Bernoulli's inequality instead of the ratio argument.

Let t ≥ 4 be an integer, g = 1 + 1/t and q = g^(t−3). Then t·g^ℓ ≥ q·(ℓ + 3) for every integer ℓ ≥ 0; in particular q ≤ t/3.
-/

theorem layered_capacity_geometric_inequality (t : ℕ) (ht : 4 ≤ t) :
    (∀ ℓ : ℕ, (1 + 1 / (t : ℝ)) ^ (t - 3) * (ℓ + 3) ≤ t * (1 + 1 / (t : ℝ)) ^ ℓ) ∧
      (1 + 1 / (t : ℝ)) ^ (t - 3) ≤ t / 3 := by
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  set g : ℝ := 1 + 1 / (t : ℝ) with hg
  have hg0 : 0 < g := by positivity
  have key : ∀ ℓ : ℕ, g ^ (t - 3) * (ℓ + 3) ≤ t * g ^ ℓ := by
    intro ℓ
    rcases le_or_gt (t - 3) ℓ with hle | hlt
    · -- ℓ = (t - 3) + j : Bernoulli for g ^ j
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hB : 1 + (j : ℝ) * (1 / t) ≤ g ^ j :=
        one_add_mul_le_pow (by have : (0 : ℝ) ≤ 1 / t := by positivity
                               linarith) j
      have hcast : ((t - 3 + j : ℕ) : ℝ) + 3 = t + j := by
        push_cast [Nat.cast_sub (show 3 ≤ t by omega)]
        ring
      rw [hcast, pow_add]
      have hpow : 0 < g ^ (t - 3) := pow_pos hg0 _
      have : (t : ℝ) + j ≤ t * g ^ j := by
        have := mul_le_mul_of_nonneg_left hB htpos.le
        rw [mul_add, mul_one, ← mul_assoc, mul_comm (t : ℝ) j, mul_assoc, mul_one_div_cancel
          htpos.ne', mul_one] at this
        linarith
      calc g ^ (t - 3) * ((t : ℝ) + j) ≤ g ^ (t - 3) * (t * g ^ j) :=
            mul_le_mul_of_nonneg_left this hpow.le
        _ = t * (g ^ (t - 3) * g ^ j) := by ring
    · -- t - 3 = ℓ + i : Bernoulli for (1 - 1/(t+1)) ^ i, whose product with g ^ i is 1
      obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_lt hlt
      set h : ℝ := 1 / ((t : ℝ) + 1) with hh
      have hh0 : 0 ≤ h := by positivity
      have hgh : g * (1 - h) = 1 := by
        rw [hg, hh]
        field_simp
        ring
      have hB : 1 + ((i + 1 : ℕ) : ℝ) * (-h) ≤ (1 - h) ^ (i + 1) := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -h by
          have : h ≤ 1 := by rw [hh, div_le_one (by linarith)]; linarith
          linarith) (i + 1)
        simpa [sub_eq_add_neg] using this
      have hcast : (ℓ : ℝ) + 3 = t - ((i + 1 : ℕ) : ℝ) := by
        have : t = ℓ + (i + 1) + 3 := by omega
        rw [this]
        push_cast
        ring
      rw [hi, show ℓ + i + 1 = ℓ + (i + 1) by ring, pow_add, hcast]
      have hgi : g ^ (i + 1) * (1 - h) ^ (i + 1) = 1 := by rw [← mul_pow, hgh, one_pow]
      have hti : (t : ℝ) - ((i + 1 : ℕ) : ℝ) ≤ t * (1 - h) ^ (i + 1) := by
        have h1 : (t : ℝ) * (1 + ((i + 1 : ℕ) : ℝ) * (-h)) ≤ t * (1 - h) ^ (i + 1) :=
          mul_le_mul_of_nonneg_left hB htpos.le
        have h2 : (t : ℝ) * h ≤ 1 := by
          rw [hh, mul_one_div, div_le_one (by linarith)]
          linarith
        have h3 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      have hpos : 0 < g ^ ℓ := pow_pos hg0 _
      have hpos' : 0 < g ^ (i + 1) := pow_pos hg0 _
      calc g ^ ℓ * g ^ (i + 1) * ((t : ℝ) - ((i + 1 : ℕ) : ℝ))
          ≤ g ^ ℓ * g ^ (i + 1) * (t * (1 - h) ^ (i + 1)) :=
            mul_le_mul_of_nonneg_left hti (by positivity)
        _ = t * g ^ ℓ * (g ^ (i + 1) * (1 - h) ^ (i + 1)) := by ring
        _ = t * g ^ ℓ := by rw [hgi, mul_one]
  refine ⟨key, ?_⟩
  have := key 0
  simp only [CharP.cast_eq_zero, zero_add, pow_zero, mul_one] at this
  linarith
