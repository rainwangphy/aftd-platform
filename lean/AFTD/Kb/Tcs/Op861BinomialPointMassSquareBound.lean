import AFTD.Prelude

/-!
# op861_binomial_point_mass_square_bound

Topic: graphs   Node: 0d7426fe0a69

Provenance: helper lemma. A binomial small-ball estimate used in the probabilistic tournament construction for OP-861.

For all natural numbers n and j, (n+1) times the square of the binomial coefficient n choose j is at most twice 4 to the n.
-/

private lemma op861_binomial_point_mass_square_bound_even_central_q (m : ℕ) : (2*(m:ℚ)+1) * (Nat.centralBinom m : ℚ)^2 ≤ 16^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hQ : ((m:ℚ)+1) * (Nat.centralBinom (m+1) : ℚ) = 2 * (2*(m:ℚ)+1) * (Nat.centralBinom m : ℚ) := by
      norm_cast
      simpa using Nat.succ_mul_centralBinom_succ m
    have hsq : ((m:ℚ)+1)^2 * (Nat.centralBinom (m+1) : ℚ)^2 = 4 * (2*(m:ℚ)+1)^2 * (Nat.centralBinom m : ℚ)^2 := by
      have h2 := congrArg (fun x : ℚ => x^2) hQ
      ring_nf at h2 ⊢
      exact h2
    have hmpos : (0:ℚ) < ((m:ℚ)+1)^2 := by positivity
    have key : ((m:ℚ)+1)^2 * ((2*((m:ℚ)+1)+1) * (Nat.centralBinom (m+1) : ℚ)^2) ≤ ((m:ℚ)+1)^2 * (16 * 16^m) := by
      nlinarith [sq_nonneg ((Nat.centralBinom m : ℚ))]
    have hgoal : (2*((m:ℚ)+1)+1) * (Nat.centralBinom (m+1) : ℚ)^2 ≤ 16 * 16^m := by
      exact le_of_mul_le_mul_left key hmpos
    simpa [pow_succ, mul_comm] using hgoal

private lemma op861_binomial_point_mass_square_bound_even_central_nat (m : ℕ) : (2*m+1) * (Nat.centralBinom m)^2 ≤ 16^m := by
  have h := op861_binomial_point_mass_square_bound_even_central_q m
  exact_mod_cast h

private lemma op861_binomial_point_mass_square_bound_odd_central_q (m : ℕ) : (2*((m:ℚ)+1)) * (Nat.choose (2*m+1) m : ℚ)^2 ≤ 8 * 16^m := by
  have hnat : Nat.centralBinom m * (2*m+1) = Nat.choose (2*m+1) m * (m+1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h := Nat.choose_mul_succ_eq (2*m) m
    have hsub : 2*m+1-m = m+1 := by omega
    simpa [hsub] using h
  have hQ : (Nat.centralBinom m : ℚ) * (2*(m:ℚ)+1) = (Nat.choose (2*m+1) m : ℚ) * ((m:ℚ)+1) := by
    exact_mod_cast hnat
  have hsq : ((m:ℚ)+1)^2 * (Nat.choose (2*m+1) m : ℚ)^2 = (2*(m:ℚ)+1)^2 * (Nat.centralBinom m : ℚ)^2 := by
    have h2 := congrArg (fun x : ℚ => x^2) hQ
    ring_nf at h2 ⊢
    exact h2.symm
  have hmpos : (0:ℚ) < ((m:ℚ)+1) := by positivity
  have ih := op861_binomial_point_mass_square_bound_even_central_q m
  have key : ((m:ℚ)+1) * ((2*((m:ℚ)+1)) * (Nat.choose (2*m+1) m : ℚ)^2) ≤ ((m:ℚ)+1) * (8 * 16^m) := by
    nlinarith [sq_nonneg (Nat.centralBinom m : ℚ)]
  exact le_of_mul_le_mul_left key hmpos

private lemma op861_binomial_point_mass_square_bound_odd_central_nat (m : ℕ) : (2*(m+1)) * (Nat.choose (2*m+1) m)^2 ≤ 8 * 16^m := by
  have h := op861_binomial_point_mass_square_bound_odd_central_q m
  exact_mod_cast h

theorem op861_binomial_point_mass_square_bound (n j : ℕ) : (n + 1) * (n.choose j) ^ 2 ≤ 2 * 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hchoose : Nat.choose (2*m) j ≤ Nat.centralBinom m := by
      have h := Nat.choose_le_middle j (2*m)
      have hdiv : (2*m)/2 = m := by omega
      rw [hdiv] at h
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact h
    have hmain := op861_binomial_point_mass_square_bound_even_central_nat m
    have h16 : (16:ℕ)^m = 4^(2*m) := by rw [show (16:ℕ) = 4^2 by norm_num, ← pow_mul]
    calc
      (2*m + 1) * (Nat.choose (2*m) j)^2 ≤ (2*m+1) * (Nat.centralBinom m)^2 := by
        gcongr
      _ ≤ 16^m := hmain
      _ = 4^(2*m) := h16
      _ ≤ 2 * 4^(2*m) := by
        have hp : 0 < (4:ℕ)^(2*m) := pow_pos (by norm_num) _
        omega
  · have hchoose : Nat.choose (2*m+1) j ≤ Nat.choose (2*m+1) m := by
      have h := Nat.choose_le_middle j (2*m+1)
      have hdiv : (2*m+1)/2 = m := by omega
      rw [hdiv] at h
      exact h
    have hmain := op861_binomial_point_mass_square_bound_odd_central_nat m
    have h8 : (8:ℕ) * 16^m = 2 * 4^(2*m+1) := by
      rw [pow_succ, show (16:ℕ)^m = 4^(2*m) by rw [show (16:ℕ) = 4^2 by norm_num, ← pow_mul]]
      ring
    calc
      (2*m+1 + 1) * (Nat.choose (2*m+1) j)^2 ≤ (2*m+1+1) * (Nat.choose (2*m+1) m)^2 := by
        gcongr
      _ = (2*(m+1)) * (Nat.choose (2*m+1) m)^2 := by ring
      _ ≤ 8 * 16^m := hmain
      _ = 2 * 4^(2*m+1) := h8
