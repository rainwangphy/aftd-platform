import AFTD.Prelude

/-!
# magic_rectangle_sos_term1

Topic: quantum   Node: 958bc121c22d

Provenance: helper lemma. step towards magic_rectangle_algebraic_sos_identity

Let A be an ℝ-algebra and let D, C, B : Fin 3 → A satisfy B j ^ 2 = 1 for all j, and every D and C commuting with every B. Setting X j = D j + C j, Z j = X j * B j, and S = ∑ j : Fin 3, X j * B j, then for any q : ℝ, ∑ j : Fin 3, (Z j - q • 1) ^ 2 = (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • 1.
-/

/-- Expansion of the first sum of squares T1 in the Magic Rectangle SOS identity. -/
theorem magic_rectangle_sos_term1
    {A : Type*} [Ring A] [Algebra ℝ A]
    (D C B : Fin 3 → A)
    (hB_sq : ∀ j, B j ^ 2 = 1)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j)
    (q : ℝ) :
    let X := fun j => D j + C j
    let Z := fun j => X j * B j
    let S := ∑ j : Fin 3, X j * B j
    ∑ j : Fin 3, (Z j - q • (1 : A)) ^ 2 =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) := by
  dsimp
  let X := fun j => D j + C j
  let Z := fun j => X j * B j
  change ∑ j : Fin 3, (Z j - q • (1 : A)) ^ 2 =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • (∑ j : Fin 3, Z j) + (3 * q ^ 2) • (1 : A)
  have hcomm (j : Fin 3) : B j * X j = X j * B j := by
    dsimp [X]
    simp only [mul_add, add_mul, ← hDB_comm j j, ← hCB_comm j j]
  have hz (j : Fin 3) : Z j * Z j = X j * X j := by
    dsimp [Z]
    calc
      (X j * B j) * (X j * B j) = X j * (B j * X j) * B j := by noncomm_ring
      _ = X j * (X j * B j) * B j := by rw [hcomm]
      _ = (X j * X j) * (B j * B j) := by noncomm_ring
      _ = X j * X j := by
        have hb : B j * B j = 1 := by simpa [pow_two] using hB_sq j
        rw [hb, mul_one]
  have hone (j : Fin 3) : (Z j - q • (1 : A)) ^ 2 =
      X j ^ 2 - (2 * q) • Z j + (q ^ 2) • (1 : A) := by
    rw [pow_two, pow_two, ← hz j]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  calc
    (∑ j : Fin 3, (Z j - q • (1 : A)) ^ 2) =
        ∑ j : Fin 3, (X j ^ 2 - (2 * q) • Z j + (q ^ 2) • (1 : A)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hone j
    _ = (∑ j : Fin 3, X j ^ 2) - (2 * q) • (∑ j : Fin 3, Z j) + (3 * q ^ 2) • (1 : A) := by
      simp only [Fin.sum_univ_three, smul_add]
      module
