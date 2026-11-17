import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleAnticommutatorIdentities

/-!
# magic_rectangle_sos_term3

Topic: quantum   Node: 6954dac8629a

Provenance: helper lemma. step towards magic_rectangle_algebraic_sos_identity

Let A be an ℝ-algebra and let D, C, B : Fin 3 → A satisfy D j ^ 2 = C j ^ 2 = B j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, pairwise commutativity within D and within C, and every D and C commuting with every B. Setting X j = D j + C j, Y j = D j - C j, W j = Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1), S = ∑ j : Fin 3, X j * B j, and J = ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1)), then for any q : ℝ, ∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2 = (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • 1 - (2 * q ^ 2) • J + (q ^ 2) • (∑ j : Fin 3, W j ^ 2).
-/

/-- Expansion of the third sum of squares T3 in the Magic Rectangle SOS identity. -/
theorem magic_rectangle_sos_term3
    {A : Type*} [Ring A] [Algebra ℝ A]
    (D C B : Fin 3 → A)
    (hD_sq : ∀ j, D j ^ 2 = 1)
    (hC_sq : ∀ j, C j ^ 2 = 1)
    (hB_sq : ∀ j, B j ^ 2 = 1)
    (hD_prod : D 0 * D 1 * D 2 = 1)
    (hC_prod : C 0 * C 1 * C 2 = -1)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j)
    (q : ℝ) :
    let X := fun j => D j + C j
    let Y := fun j => D j - C j
    let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
    let S := ∑ j : Fin 3, X j * B j
    let J := ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1))
    ∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2 =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) -
      (2 * q ^ 2) • J + (q ^ 2) • (∑ j : Fin 3, W j ^ 2) := by
  dsimp
  let X := fun j => D j + C j
  let Y := fun j => D j - C j
  let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
  let S := ∑ j : Fin 3, X j * B j
  let J := ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1))
  change (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) -
      (2 * q ^ 2) • J + (q ^ 2) • (∑ j : Fin 3, W j ^ 2)
  have hXB (j : Fin 3) : B j * X j = X j * B j := by
    dsimp [X]
    simp only [mul_add, add_mul, ← hDB_comm j j, ← hCB_comm j j]
  have hXBsum : (∑ j : Fin 3, (X j * B j + B j * X j)) = (2 : ℝ) • S := by
    simp only [Fin.sum_univ_three]
    rw [hXB 0, hXB 1, hXB 2]
    dsimp [S]
    simp only [Fin.sum_univ_three, smul_add]
    module
  have hBsum : (∑ j : Fin 3, B j ^ 2) = (3 : ℝ) • (1 : A) := by
    simp only [hB_sq, Fin.sum_univ_three]
    module
  have hall := magic_rectangle_anticommutator_identities D C B hD_sq hC_sq hB_sq
      hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm
  have hXW : (∑ j : Fin 3, (X j * W j + W j * X j)) = (4 : ℝ) • S := by
    have h : (∑ j : Fin 3, (X j * W j + W j * X j)) = (4 : A) * S := hall.2.2.2
    rw [h, Algebra.smul_def, map_ofNat]
  have hWB : (∑ j : Fin 3, (W j * B j + B j * W j)) = (2 : ℝ) • J := by
    have h : (∑ j : Fin 3, (W j * B j + B j * W j)) = (2 : A) * J := hall.2.1
    rw [h, Algebra.smul_def, map_ofNat]
  have hexpand : (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) =
      (∑ j : Fin 3, X j ^ 2) + q • (∑ j : Fin 3, (X j * B j + B j * X j)) -
      q • (∑ j : Fin 3, (X j * W j + W j * X j)) +
      (q ^ 2) • (∑ j : Fin 3, B j ^ 2) -
      (q ^ 2) • (∑ j : Fin 3, (W j * B j + B j * W j)) +
      (q ^ 2) • (∑ j : Fin 3, W j ^ 2) := by
    simp only [Fin.sum_univ_three, pow_two, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub]
    module
  rw [hexpand, hXBsum, hXW, hBsum, hWB]
  simp only [smul_smul]
  module
