import AFTD.Prelude

/-!
# open_network_kernels_anticommute

Topic: quantum   Node: a62e1bd97345

Provenance: formalization of a published result. Source: arXiv:2610.35838 Appendix E, Eq. (61)

In any ring, dichotomic observables A_0, A_1 and B_0, B_1 squaring to 1 that commute with each other yield anticommuting kernel operators: (A_0 * B_0 - A_1 * B_1) * (A_0 * B_1 + A_1 * B_0) + (A_0 * B_1 + A_1 * B_0) * (A_0 * B_0 - A_1 * B_1) = 0.
-/

/-- The open network kernels U_0 and U_1 anticommute in any dimension. -/
theorem open_network_kernels_anticommute
    {R : Type*} [Ring R] (A₀ A₁ B₀ B₁ : R)
    (hA₀ : A₀ ^ 2 = 1) (hA₁ : A₁ ^ 2 = 1)
    (hB₀ : B₀ ^ 2 = 1) (hB₁ : B₁ ^ 2 = 1)
    (hAB00 : A₀ * B₀ = B₀ * A₀)
    (hAB01 : A₀ * B₁ = B₁ * A₀)
    (hAB10 : A₁ * B₀ = B₀ * A₁)
    (hAB11 : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ - A₁ * B₁) * (A₀ * B₁ + A₁ * B₀) +
    (A₀ * B₁ + A₁ * B₀) * (A₀ * B₀ - A₁ * B₁) = 0 := by
  have hXZ : (A₀ * B₀) * (A₀ * B₁) = B₀ * B₁ := by
    rw [hAB00, mul_assoc, ← mul_assoc A₀ A₀ B₁, ← sq, hA₀, one_mul]
  have hXW : (A₀ * B₀) * (A₁ * B₀) = A₀ * A₁ := by
    rw [mul_assoc, hAB10, ← mul_assoc B₀ B₀ A₁, ← mul_assoc A₀ (B₀ * B₀) A₁, ← sq, hB₀, mul_one]
  have hYZ : (A₁ * B₁) * (A₀ * B₁) = A₁ * A₀ := by
    rw [mul_assoc, ← mul_assoc B₁ A₀ B₁, ← hAB01, mul_assoc, ← sq, hB₁, mul_one]
  have hYW : (A₁ * B₁) * (A₁ * B₀) = B₁ * B₀ := by
    rw [hAB11, mul_assoc, ← mul_assoc A₁ A₁ B₀, ← sq, hA₁, one_mul]
  have hZX : (A₀ * B₁) * (A₀ * B₀) = B₁ * B₀ := by
    rw [hAB01, mul_assoc, ← mul_assoc A₀ A₀ B₀, ← sq, hA₀, one_mul]
  have hZY : (A₀ * B₁) * (A₁ * B₁) = A₀ * A₁ := by
    rw [mul_assoc, ← mul_assoc B₁ A₁ B₁, ← hAB11, mul_assoc, ← sq, hB₁, mul_one]
  have hWX : (A₁ * B₀) * (A₀ * B₀) = A₁ * A₀ := by
    rw [mul_assoc, ← mul_assoc B₀ A₀ B₀, ← hAB00, mul_assoc, ← sq, hB₀, mul_one]
  have hWY : (A₁ * B₀) * (A₁ * B₁) = B₀ * B₁ := by
    rw [hAB10, mul_assoc, ← mul_assoc A₁ A₁ B₁, ← sq, hA₁, one_mul]
  simp only [sub_mul, mul_add, add_mul, mul_sub]
  rw [hXZ, hXW, hYZ, hYW, hZX, hZY, hWX, hWY]
  abel
