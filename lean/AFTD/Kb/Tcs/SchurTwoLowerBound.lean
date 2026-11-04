import AFTD.Prelude

/-!
# schur_two_lower_bound

Topic: combinatorics   Node: 97fb83fd77eb

Provenance: helper lemma. arXiv:2611.01714 Proposition 3.1

For every integer k ≥ 3, the 2-coloring of Fin (k^2 + k - 2) that assigns color 0 when x.val + 1 ≤ k - 1 ∨ k^2 ≤ x.val + 1 and color 1 otherwise contains no monochromatic solution to (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1.
-/

/-- For every integer k ≥ 3, the 2-coloring of Fin (k^2 + k - 2) with A₁ = [1, k-1] ∪ [k^2, k^2+k-2] and A₂ = [k, k^2-1] contains no monochromatic solution to (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1. -/
theorem schur_two_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ x y z : Fin (k^2 + k - 2),
      (if x.val + 1 ≤ k - 1 ∨ k^2 ≤ x.val + 1 then (0 : Fin 2) else 1) =
        (if y.val + 1 ≤ k - 1 ∨ k^2 ≤ y.val + 1 then (0 : Fin 2) else 1) ∧
      (if y.val + 1 ≤ k - 1 ∨ k^2 ≤ y.val + 1 then (0 : Fin 2) else 1) =
        (if z.val + 1 ≤ k - 1 ∨ k^2 ≤ z.val + 1 then (0 : Fin 2) else 1) ∧
      (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1 := by
  intro ⟨x, y, z, hxy, hyz, heq⟩
  set vx := x.val + 1
  set vy := y.val + 1
  set vz := z.val + 1
  have hz_lt : vz ≤ k^2 + k - 2 := by
    have := z.isLt
    omega
  have hvx_pos : 1 ≤ vx := by omega
  have hvy_pos : 1 ≤ vy := by omega
  by_cases hx : vx ≤ k - 1 ∨ k^2 ≤ vx
  · -- Color 0
    simp only [hx, ↓reduceIte] at hxy
    have hy : vy ≤ k - 1 ∨ k^2 ≤ vy := by
      by_contra hny
      simp [hny] at hxy
    simp only [hy, ↓reduceIte] at hyz
    have hz : vz ≤ k - 1 ∨ k^2 ≤ vz := by
      by_contra hnz
      simp [hnz] at hyz
    rcases hy with hy | hy
    · -- vy ≤ k - 1
      rcases hx with hx | hx
      · -- vx ≤ k - 1
        have h_low1 : (k - 1) * 1 ≤ (k - 1) * vy := Nat.mul_le_mul_left _ hvy_pos
        have h_low : k ≤ vz := by omega
        have h_up1 : (k - 1) * vy ≤ (k - 1) * (k - 1) := Nat.mul_le_mul_left _ hy
        have h_up3 : (k - 1) * k < k^2 := by
          have hk_pos : 0 < k := by omega
          have h_lt : k - 1 < k := by omega
          have := Nat.mul_lt_mul_of_pos_right h_lt hk_pos
          rw [sq]
          omega
        have h_up : vz ≤ (k - 1) * k := by
          have : vx + (k - 1) * vy ≤ (k - 1) + (k - 1) * (k - 1) := by omega
          have : (k - 1) + (k - 1) * (k - 1) = (k - 1) * k := by
            have : 1 ≤ k := by omega
            zify [this]
            ring
          omega
        omega
      · -- k^2 ≤ vx
        have : (k - 1) * 1 ≤ (k - 1) * vy := Nat.mul_le_mul_left _ hvy_pos
        omega
    · -- k^2 ≤ vy
      have : (k - 1) * k^2 ≤ (k - 1) * vy := Nat.mul_le_mul_left _ hy
      have hk' : 2 ≤ k - 1 := by omega
      have : 2 * k^2 ≤ (k - 1) * k^2 := Nat.mul_le_mul_right (k^2) hk'
      have : k ≤ k^2 := Nat.le_self_pow (by omega) k
      omega
  · -- Color 1
    simp only [hx, ↓reduceIte] at hxy
    have hy : ¬(vy ≤ k - 1 ∨ k^2 ≤ vy) := by
      intro hy'
      simp [hy'] at hxy
    simp only [hy, ↓reduceIte] at hyz
    have hz : ¬(vz ≤ k - 1 ∨ k^2 ≤ vz) := by
      intro hz'
      simp [hz'] at hyz
    have hk1 : k ≤ vx := by omega
    have hk2 : k ≤ vy := by omega
    have hk3 : vz < k^2 := by omega
    have h_bound : k^2 ≤ vz := by
      calc k^2 = k + (k - 1) * k := by
            have : 1 ≤ k := by omega
            zify [this]
            ring
        _ ≤ vx + (k - 1) * vy := by
            have : (k - 1) * k ≤ (k - 1) * vy := Nat.mul_le_mul_left _ hk2
            omega
        _ = vz := heq
    omega
