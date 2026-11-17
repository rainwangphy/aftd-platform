import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleAnticommutatorIdentities

/-!
# magic_rectangle_sos_term2

Topic: quantum   Node: d78ee014db69

Provenance: helper lemma. step towards magic_rectangle_algebraic_sos_identity

Let A be an ℝ-algebra and let D, C, B : Fin 3 → A satisfy D j ^ 2 = C j ^ 2 = B j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, pairwise commutativity within D and within C, and every D and C commuting with every B. Setting X j = D j + C j, Y j = D j - C j, V j = X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1), and S = ∑ j : Fin 3, X j * B j, then for any r : ℝ, ∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2 = (∑ j : Fin 3, Y j ^ 2) - (4 / r) • S + ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2).
-/

/-- Expansion of the second sum of squares T2 in the Magic Rectangle SOS identity. -/
theorem magic_rectangle_sos_term2
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
    (r : ℝ) :
    let X := fun j => D j + C j
    let Y := fun j => D j - C j
    let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
    let S := ∑ j : Fin 3, X j * B j
    ∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2 =
      (∑ j : Fin 3, Y j ^ 2) - (4 / r) • S + ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2) := by
  dsimp
  let X := fun j => D j + C j
  let Y := fun j => D j - C j
  let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
  let S := ∑ j : Fin 3, X j * B j
  change ∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2 =
      (∑ j : Fin 3, Y j ^ 2) - (4 / r) • S + ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2)
  have hcross : (∑ j : Fin 3, (Y j * V j + V j * Y j)) = 4 * S := by
    exact (magic_rectangle_anticommutator_identities D C B hD_sq hC_sq hB_sq
      hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm).2.2.1
  have hexpand : (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) =
      (∑ j : Fin 3, Y j ^ 2) - (1 / r) • (∑ j : Fin 3, (Y j * V j + V j * Y j)) +
        ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2) := by
    simp only [Fin.sum_univ_three, pow_two, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, smul_smul, smul_add, smul_sub]
    module
  have hfour : (4 : A) * S = (4 : ℝ) • S := by
    rw [Algebra.smul_def, map_ofNat]
  rw [hexpand, hcross, hfour, smul_smul]
  have hc : (1 / r) * 4 = 4 / r := by ring
  rw [hc]
