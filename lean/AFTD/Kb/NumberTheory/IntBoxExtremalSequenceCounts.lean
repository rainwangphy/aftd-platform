import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# int_box_extremal_sequence_counts

Topic: elementary_number_theory   Node: e05243933186

Provenance: helper lemma. The minimality of S(m) in arXiv:2610.16562 (The Davenport constant of low-dimensional boxes) (proof of Theorem 1): the only zero-sum subsequences of S(m) are empty or all of it.

If integers A, B, C with 0 ≤ C ≤ M(2M−1) satisfy A·(M, M) + B·(−M, M−1) + C·(M−Q, −M) = 0, where M ≥ 2, gcd(M, Q) = 1 and gcd(2M−1, 2M−Q) = 1, then (A, B, C) is (0, 0, 0) or (Q(M−1)+M, M(2M−Q), M(2M−1)).
-/

theorem int_box_extremal_sequence_counts (M Q A B C : ℤ) (hM : 2 ≤ M)
    (hcopMQ : IsCoprime M Q) (hcopZ : IsCoprime (2 * M - 1) (2 * M - Q))
    (hC0 : 0 ≤ C) (hCle : C ≤ M * (2 * M - 1))
    (ex : A * M - B * M + C * (M - Q) = 0) (ey : A * M + B * (M - 1) - C * M = 0) :
    (A = 0 ∧ B = 0 ∧ C = 0) ∨
      (A = Q * (M - 1) + M ∧ B = M * (2 * M - Q) ∧ C = M * (2 * M - 1)) := by
  have hMpos : 0 < M := by linarith
  have hMB : M ∣ B := ⟨A + B - C, by linear_combination -1 * ey⟩
  have hMC : M ∣ C := by
    have : M ∣ C * Q := ⟨A - B + C, by linear_combination -1 * ex⟩
    exact hcopMQ.dvd_of_dvd_mul_right this
  obtain ⟨B', hB'⟩ := hMB
  obtain ⟨C', hC'⟩ := hMC
  subst hB' hC'
  have hA : A = C' * M - B' * (M - 1) := by
    have : M * (A + B' * (M - 1) - C' * M) = 0 := by linear_combination ey
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hA
  have hrel : B' * (2 * M - 1) = C' * (2 * M - Q) := by
    have : M * (B' * (2 * M - 1) - C' * (2 * M - Q)) = 0 := by linear_combination -1 * ex
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hdvd : (2 * M - 1) ∣ C' := by
    have : (2 * M - 1) ∣ C' * (2 * M - Q) := ⟨B', by linear_combination -1 * hrel⟩
    exact hcopZ.dvd_of_dvd_mul_right this
  obtain ⟨j, hj⟩ := hdvd
  subst hj
  have hP : 0 < M * (2 * M - 1) := by nlinarith
  have hj0 : 0 ≤ j := by
    by_contra h
    push_neg at h
    nlinarith [mul_neg_of_pos_of_neg hP h]
  have hj1 : j ≤ 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ j by omega) hP.le]
  have h2 : 0 < 2 * M - 1 := by linarith
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · left
    have hB0 : B' = 0 := by
      have : B' * (2 * M - 1) = 0 := by rw [hrel]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    subst hB0
    refine ⟨by ring, by ring, by ring⟩
  · right
    have hB1 : B' = 2 * M - Q := by
      have : (2 * M - 1) * (B' - (2 * M - Q)) = 0 := by linear_combination hrel
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    subst hB1
    refine ⟨by ring, by ring, by ring⟩
