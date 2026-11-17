import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleAlgebraicSosIdentity

/-!
# magic_rectangle_sos_certificate

Topic: quantum   Node: c75d376beace

Provenance: formalization of a published result. Source: arXiv:2610.12001 Theorem 3.1

Let H be a complex Hilbert space and let D, C, B : Fin 3 → (H →L[ℂ] H) be self-adjoint continuous linear operators satisfying D j ^ 2 = 1, C j ^ 2 = 1, and B j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, D j * D k = D k * D j, C j * C k = C k * C j, D j * B k = B k * D j, and C j * B k = B k * C j for all j, k. Setting X j = D j + C j, Y j = D j - C j, Z j = X j * B j, V j = X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1), W j = Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1), S = ∑ j : Fin 3, X j * B j, r = Real.sqrt 6, and q = 2 * r / 3, then the exact sum-of-squares certificate identity holds: (2 * r) • 1 - S = (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) + (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) + (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2).
-/

/-- Exact sum-of-squares certificate for the 2x3 magic rectangle Bell operator. -/
theorem magic_rectangle_sos_certificate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D C B : Fin 3 → (H →L[ℂ] H))
    (hD_sa : ∀ j, IsSelfAdjoint (D j))
    (hC_sa : ∀ j, IsSelfAdjoint (C j))
    (hB_sa : ∀ j, IsSelfAdjoint (B j))
    (hD_sq : ∀ j, D j ^ 2 = 1)
    (hC_sq : ∀ j, C j ^ 2 = 1)
    (hB_sq : ∀ j, B j ^ 2 = 1)
    (hD_prod : D 0 * D 1 * D 2 = 1)
    (hC_prod : C 0 * C 1 * C 2 = -1)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j) :
    let X : Fin 3 → (H →L[ℂ] H) := fun j => D j + C j
    let Y : Fin 3 → (H →L[ℂ] H) := fun j => D j - C j
    let Z : Fin 3 → (H →L[ℂ] H) := fun j => X j * B j
    let V : Fin 3 → (H →L[ℂ] H) := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
    let W : Fin 3 → (H →L[ℂ] H) := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
    let S : H →L[ℂ] H := ∑ j : Fin 3, X j * B j
    let r : ℝ := Real.sqrt 6
    let q : ℝ := 2 * r / 3
    (2 * r) • (1 : H →L[ℂ] H) - S =
      (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) +
      (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) +
      (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) := by
  exact magic_rectangle_algebraic_sos_identity D C B hD_sq hC_sq hB_sq
    hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm
