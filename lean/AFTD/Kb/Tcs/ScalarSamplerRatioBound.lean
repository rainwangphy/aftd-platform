import AFTD.Prelude

/-!
# scalar_sampler_ratio_bound

Topic: information   Node: e4d5e6ec964b

Provenance: helper lemma. arXiv:2611.13281, Lemma 2.1, equation (7)

For integers q ≥ 3, r ≥ 1 and 0 ≤ j < q, the parameters m_j = 1 + (q-1)!(12r(q-1) + j), D = ∏_{i=0}^{q-1} m_i, M = 12r(D/m_0)^2, and S = (12r-1) m_0 (D/m_0)^2 satisfy m_j / S ≤ 2 / M.
-/

/-- Ratio bound m_j / S ≤ 2 / M for the scalar quadratic sampler parameters. -/
theorem scalar_sampler_ratio_bound (q r : ℕ) (hq : 3 ≤ q) (hr : 1 ≤ r) (j : ℕ) (hj : j < q) :
    let m : ℕ → ℤ := fun i => 1 + (q - 1).factorial * (12 * r * (q - 1) + i)
    let D : ℤ := ∏ i ∈ Finset.range q, m i
    let M : ℤ := 12 * r * (D / m 0) ^ 2
    let S : ℤ := (12 * r - 1) * m 0 * (D / m 0) ^ 2
    (m j : ℝ) / (S : ℝ) ≤ 2 / (M : ℝ) := by
  intro m D M S
  set K := ((D / m 0 : ℤ) : ℝ) ^ 2
  have hM_eq : (M : ℝ) = 12 * (r : ℝ) * K := by
    dsimp [M, K]
    push_cast
    ring
  have hS_eq : (S : ℝ) = (12 * (r : ℝ) - 1) * (m 0 : ℝ) * K := by
    dsimp [S, K]
    push_cast
    ring
  rcases eq_or_ne ((D / m 0 : ℤ) : ℝ) 0 with h | h
  · have hK0 : K = 0 := by
      dsimp [K]
      rw [h]
      ring
    have hS0 : (S : ℝ) = 0 := by rw [hS_eq, hK0, mul_zero]
    have hM0 : (M : ℝ) = 0 := by rw [hM_eq, hK0, mul_zero]
    rw [hS0, hM0, div_zero, div_zero]
  · have hK : 0 < K := sq_pos_of_ne_zero h
    set R := (r : ℝ)
    set Q := (q : ℝ) - 1
    set J := (j : ℝ)
    set F := ((q - 1).factorial : ℝ)
    have hR : 1 ≤ R := by
      dsimp [R]
      exact_mod_cast hr
    have hQ : 2 ≤ Q := by
      have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      dsimp [Q]
      linarith
    have hF : 1 ≤ F := by
      have : 1 ≤ (q - 1).factorial := Nat.factorial_pos (q - 1)
      dsimp [F]
      exact_mod_cast this
    have hJ : J ≤ Q := by
      have : j + 1 ≤ q := hj
      have : (j : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast this
      dsimp [J, Q]
      linarith
    have hm0 : (m 0 : ℝ) = 1 + F * (12 * R * Q) := by
      dsimp [m, F, R, Q]
      push_cast
      ring
    have hmj : (m j : ℝ) = 1 + F * (12 * R * Q + J) := by
      dsimp [m, F, R, Q, J]
      push_cast
      ring
    have hm0_pos : 0 < (m 0 : ℝ) := by
      rw [hm0]
      have : 0 < F := by linarith
      have : 0 < R := by linarith
      have : 0 < Q := by linarith
      positivity
    have hM_pos : 0 < (M : ℝ) := by
      rw [hM_eq]
      have : 0 < R := by linarith
      positivity
    have hS_pos : 0 < (S : ℝ) := by
      rw [hS_eq]
      have : 0 < 12 * R - 1 := by linarith
      positivity
    rw [div_le_div_iff₀ hS_pos hM_pos]
    rw [hM_eq, hS_eq]
    have h_diff : (m j : ℝ) * (12 * R) ≤ 2 * (12 * R - 1) * (m 0 : ℝ) := by
      have hid : 2 * (12 * R - 1) * (m 0 : ℝ) - (m j : ℝ) * (12 * R) =
          (12 * R - 2) + (12 * R - 3) * (12 * R * Q * F) + 12 * R * F * (Q - J) := by
        rw [hm0, hmj]
        ring
      have h1 : 0 ≤ 12 * R - 2 := by linarith
      have h2 : 0 ≤ 12 * R - 3 := by linarith
      have h3 : 0 ≤ 12 * R * Q * F := by positivity
      have h4 : 0 ≤ 12 * R * F := by positivity
      have h5 : 0 ≤ Q - J := by linarith
      have h_nonneg : 0 ≤ (12 * R - 2) + (12 * R - 3) * (12 * R * Q * F) + 12 * R * F * (Q - J) := by
        positivity
      linarith
    calc (m j : ℝ) * (12 * (r : ℝ) * K)
      _ = ((m j : ℝ) * (12 * R)) * K := by ring
      _ ≤ (2 * (12 * R - 1) * (m 0 : ℝ)) * K := by nlinarith
      _ = 2 * ((12 * (r : ℝ) - 1) * (m 0 : ℝ) * K) := by ring
