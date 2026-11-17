import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleAnticommutatorIdentities
import AFTD.Kb.Tcs.MagicRectangleSosTerm1
import AFTD.Kb.Tcs.MagicRectangleSosTerm2
import AFTD.Kb.Tcs.MagicRectangleSosTerm3
import AFTD.Kb.Tcs.MagicRectangleRowRelations

/-!
# magic_rectangle_algebraic_sos_identity

Topic: quantum   Node: 0af81bd320dd

Provenance: helper lemma. arXiv:2610.12001, Eq. (10)

Let A be an ℝ-algebra and let D, C, B : Fin 3 → A satisfy D j ^ 2 = C j ^ 2 = B j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, pairwise commutativity within D and within C, and every D and C commuting with every B. Setting X j = D j + C j, Y j = D j - C j, Z j = X j * B j, V j = X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1), W j = Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1), S = ∑ j : Fin 3, X j * B j, r = Real.sqrt 6, and q = 2 * r / 3, then (2 * r) • 1 - S = (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) + (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) + (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2).
-/

theorem in937_rectangle_sos_combine
    {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (hr : 0 < r) (hr2 : r ^ 2 = 6)
    (X Y V W S J I : A)
    (hxy : X + Y = (12 : ℝ) • I)
    (hvw : V + W = (24 : ℝ) • I + (2 : ℝ) • J) :
    let q := 2 * r / 3
    (2 * r) • I - S =
      (5 * r / 64) • (X - (2 * q) • S + (3 * q ^ 2) • I) +
      (r / 12) • (Y - (4 / r) • S + ((1 / r) ^ 2) • V) +
      (r / 192) • (X - (2 * q) • S + (3 * q ^ 2) • I - (2 * q ^ 2) • J + (q ^ 2) • W) := by
  dsimp
  let q := 2 * r / 3
  let u := r / 12
  let v := (r / 192) * q ^ 2
  let s := -(5 * r / 64) * (2 * q) - (r / 12) * (4 / r) - (r / 192) * (2 * q)
  let j := -(r / 192) * (2 * q ^ 2)
  let i := (5 * r / 64) * (3 * q ^ 2) + (r / 192) * (3 * q ^ 2)
  have hne : r ≠ 0 := ne_of_gt hr
  have hr3 : r ^ 3 = 6 * r := by
    calc
      r ^ 3 = r * (r ^ 2) := by ring
      _ = r * 6 := by rw [hr2]
      _ = 6 * r := by ring
  have hr4 : r ^ 4 = 36 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = 36 := by rw [hr2]; norm_num
  have hX : 5 * r / 64 + r / 192 = u := by dsimp [u]; ring
  have hV : (r / 12) * (1 / r) ^ 2 = v := by
    dsimp [v, q]
    field_simp [hne]
    nlinarith [hr2, hr3, hr4]
  have hS : s = -1 := by
    dsimp [s, q]
    field_simp [hne]
    nlinarith [hr2, hr3, hr4]
  have hJ : 2 * v + j = 0 := by dsimp [v, j]; ring
  have hI : 12 * u + 24 * v + i = 2 * r := by
    dsimp [u, v, i, q]
    nlinarith [hr2, hr3, hr4]
  have hcollect :
      (5 * r / 64) • (X - (2 * q) • S + (3 * q ^ 2) • I) +
      (r / 12) • (Y - (4 / r) • S + ((1 / r) ^ 2) • V) +
      (r / 192) • (X - (2 * q) • S + (3 * q ^ 2) • I - (2 * q ^ 2) • J + (q ^ 2) • W) =
      u • (X + Y) + v • (V + W) + s • S + j • J + i • I := by
    simp only [smul_add, smul_sub, smul_smul]
    rw [hV]
    dsimp [u, s, j, i]
    module
  change (2 * r) • I - S =
      (5 * r / 64) • (X - (2 * q) • S + (3 * q ^ 2) • I) +
      (r / 12) • (Y - (4 / r) • S + ((1 / r) ^ 2) • V) +
      (r / 192) • (X - (2 * q) • S + (3 * q ^ 2) • I - (2 * q ^ 2) • J + (q ^ 2) • W)
  rw [hcollect, hxy, hvw]
  calc
    (2 * r) • I - S = (12 * u + 24 * v + i) • I + s • S + (2 * v + j) • J := by
      rw [hI, hS, hJ]
      simp [sub_eq_add_neg]
    _ = u • ((12 : ℝ) • I) + v • ((24 : ℝ) • I + (2 : ℝ) • J) + s • S + j • J + i • I := by
      simp only [smul_add, smul_smul]
      module

/-- The exact algebraic sum-of-squares identity for the magic rectangle Bell operator in a real algebra. -/
theorem magic_rectangle_algebraic_sos_identity
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
    (hCB_comm : ∀ j k, C j * B k = B k * C j) :
    let X := fun j => D j + C j
    let Y := fun j => D j - C j
    let Z := fun j => X j * B j
    let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
    let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
    let S := ∑ j : Fin 3, X j * B j
    let r : ℝ := Real.sqrt 6
    let q : ℝ := 2 * r / 3
    (2 * r) • (1 : A) - S =
      (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) +
      (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) +
      (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) := by
  dsimp
  let X := fun j => D j + C j
  let Y := fun j => D j - C j
  let Z := fun j => X j * B j
  let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
  let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
  let S := ∑ j : Fin 3, X j * B j
  let J := ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1))
  let r : ℝ := Real.sqrt 6
  let q : ℝ := 2 * r / 3
  change (2 * r) • (1 : A) - S =
      (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) +
      (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) +
      (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : r ^ 2 = 6 := by dsimp [r]; norm_num
  have h0 : X 0 ^ 2 + Y 0 ^ 2 = (4 : A) :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 0).1
  have h1 : X 1 ^ 2 + Y 1 ^ 2 = (4 : A) :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 1).1
  have h2 : X 2 ^ 2 + Y 2 ^ 2 = (4 : A) :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 2).1
  have hxy : (∑ j : Fin 3, X j ^ 2) + (∑ j : Fin 3, Y j ^ 2) = (12 : ℝ) • (1 : A) := by
    calc
      _ = (X 0 ^ 2 + Y 0 ^ 2) + (X 1 ^ 2 + Y 1 ^ 2) + (X 2 ^ 2 + Y 2 ^ 2) := by
        simp only [Fin.sum_univ_three]
        abel
      _ = (4 : A) + 4 + 4 := by rw [h0, h1, h2]
      _ = (12 : ℝ) • (1 : A) := by rw [Algebra.smul_def, map_ofNat, mul_one]; norm_num
  have hvw : (∑ j : Fin 3, V j ^ 2) + (∑ j : Fin 3, W j ^ 2) =
      (24 : ℝ) • (1 : A) + (2 : ℝ) • J := by
    have hall := (magic_rectangle_anticommutator_identities D C B hD_sq hC_sq hB_sq
      hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm).1
    have h24 : (24 : A) = (24 : ℝ) • (1 : A) := by rw [Algebra.smul_def, map_ofNat, mul_one]
    have h2J : (2 : A) * J = (2 : ℝ) • J := by rw [Algebra.smul_def, map_ofNat]
    calc
      _ = ∑ j : Fin 3, (V j ^ 2 + W j ^ 2) := by
        simp only [Fin.sum_univ_three]
        abel
      _ = (24 : A) + (2 : A) * J := hall
      _ = (24 : ℝ) • (1 : A) + (2 : ℝ) • J := by rw [h24, h2J]
  have ht1 : (∑ j : Fin 3, (Z j - q • (1 : A)) ^ 2) =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) :=
    magic_rectangle_sos_term1 D C B hB_sq hDB_comm hCB_comm q
  have ht2 : (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) =
      (∑ j : Fin 3, Y j ^ 2) - (4 / r) • S + ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2) :=
    magic_rectangle_sos_term2 D C B hD_sq hC_sq hB_sq hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm r
  have ht3 : (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) =
      (∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) -
        (2 * q ^ 2) • J + (q ^ 2) • (∑ j : Fin 3, W j ^ 2) :=
    magic_rectangle_sos_term3 D C B hD_sq hC_sq hB_sq hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm q
  have h := in937_rectangle_sos_combine r hr hr2 (∑ j : Fin 3, X j ^ 2)
    (∑ j : Fin 3, Y j ^ 2) (∑ j : Fin 3, V j ^ 2) (∑ j : Fin 3, W j ^ 2) S J (1 : A) hxy hvw
  change (2 * r) • (1 : A) - S =
      (5 * r / 64) • ((∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A)) +
      (r / 12) • ((∑ j : Fin 3, Y j ^ 2) - (4 / r) • S + ((1 / r) ^ 2) • (∑ j : Fin 3, V j ^ 2)) +
      (r / 192) • ((∑ j : Fin 3, X j ^ 2) - (2 * q) • S + (3 * q ^ 2) • (1 : A) - (2 * q ^ 2) • J + (q ^ 2) • (∑ j : Fin 3, W j ^ 2)) at h
  rw [← ht3, ← ht2, ← ht1] at h
  exact h
