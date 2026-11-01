import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleRowRelations
import AFTD.Kb.Tcs.V

/-!
# magic_rectangle_anticommutator_identities

Topic: quantum   Node: 38e7859949e1

Provenance: helper lemma. arXiv:2610.12001, Eqs. (12)-(14)

Let A be a ring and let D, C, B : Fin 3 → A satisfy D j ^ 2 = C j ^ 2 = B j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, pairwise commutativity within D and within C, and every D and C commuting with every B. Setting X j = D j + C j, Y j = D j - C j, V j = X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1), W j = Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1), S = ∑ j : Fin 3, X j * B j, and J = ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1)), then ∑ j : Fin 3, (V j ^ 2 + W j ^ 2) = 24 + 2 * J, ∑ j : Fin 3, (W j * B j + B j * W j) = 2 * J, ∑ j : Fin 3, (Y j * V j + V j * Y j) = 4 * S, and ∑ j : Fin 3, (X j * W j + W j * X j) = 4 * S.
-/

lemma magic_rectangle_anticommutator_identities_fin3_idx_01 : (0 : Fin 3) + 1 = 1 := rfl
lemma magic_rectangle_anticommutator_identities_fin3_idx_02 : (0 : Fin 3) + 2 = 2 := rfl
lemma magic_rectangle_anticommutator_identities_fin3_idx_11 : (1 : Fin 3) + 1 = 2 := rfl
lemma magic_rectangle_anticommutator_identities_fin3_idx_12 : (1 : Fin 3) + 2 = 0 := rfl
lemma magic_rectangle_anticommutator_identities_fin3_idx_21 : (2 : Fin 3) + 1 = 0 := rfl
lemma magic_rectangle_anticommutator_identities_fin3_idx_22 : (2 : Fin 3) + 2 = 1 := rfl

lemma magic_rectangle_anticommutator_identities_mul_XB_comm {A : Type*} [Ring A] (D C B : Fin 3 → A)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j)
    (j k : Fin 3) :
    (D j + C j) * B k = B k * (D j + C j) := by
  calc (D j + C j) * B k
    _ = D j * B k + C j * B k := by noncomm_ring
    _ = B k * D j + B k * C j := by rw [hDB_comm, hCB_comm]
    _ = B k * (D j + C j) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_mul_YB_comm {A : Type*} [Ring A] (D C B : Fin 3 → A)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j)
    (j k : Fin 3) :
    (D j - C j) * B k = B k * (D j - C j) := by
  calc (D j - C j) * B k
    _ = D j * B k - C j * B k := by noncomm_ring
    _ = B k * D j - B k * C j := by rw [hDB_comm, hCB_comm]
    _ = B k * (D j - C j) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_row_rel_rev1 {A : Type*} [Ring A] (D C : Fin 3 → A)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (i k : Fin 3) :
    let X := fun m => D m + C m
    let Y := fun m => D m - C m
    X k * X i + Y k * Y i = X i * X k + Y i * Y k := by
  intro X Y
  change (D k + C k) * (D i + C i) + (D k - C k) * (D i - C i) = (D i + C i) * (D k + C k) + (D i - C i) * (D k - C k)
  calc (D k + C k) * (D i + C i) + (D k - C k) * (D i - C i)
    _ = 2 * (D k * D i + C k * C i) := by noncomm_ring
    _ = 2 * (D i * D k + C i * C k) := by rw [hD_comm k i, hC_comm k i]
    _ = (D i + C i) * (D k + C k) + (D i - C i) * (D k - C k) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_row_rel_rev2 {A : Type*} [Ring A] (D C : Fin 3 → A)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (i k : Fin 3) :
    let X := fun m => D m + C m
    let Y := fun m => D m - C m
    X k * Y i + Y k * X i = X i * Y k + Y i * X k := by
  intro X Y
  change (D k + C k) * (D i - C i) + (D k - C k) * (D i + C i) = (D i + C i) * (D k - C k) + (D i - C i) * (D k + C k)
  calc (D k + C k) * (D i - C i) + (D k - C k) * (D i + C i)
    _ = 2 * (D k * D i - C k * C i) := by noncomm_ring
    _ = 2 * (D i * D k - C i * C k) := by rw [hD_comm k i, hC_comm k i]
    _ = (D i + C i) * (D k - C k) + (D i - C i) * (D k + C k) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_B_mul_Y_mul {A : Type*} [Ring A] (Y B : Fin 3 → A)
    (hYB_comm : ∀ j k, Y j * B k = B k * Y j)
    (j i k : Fin 3) :
    B j * (Y i * B k) = Y i * (B j * B k) := by
  calc B j * (Y i * B k)
    _ = (B j * Y i) * B k := by noncomm_ring
    _ = (Y i * B j) * B k := by rw [hYB_comm i j]
    _ = Y i * (B j * B k) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_YV_add_VY {A : Type*} [Ring A] (X Y B : Fin 3 → A)
    (hYB_comm : ∀ j k, Y j * B k = B k * Y j)
    (j : Fin 3) :
    let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
    Y j * V j + V j * Y j =
      (Y j * X (j + 1) + X (j + 1) * Y j) * B (j + 2) +
      (Y j * X (j + 2) + X (j + 2) * Y j) * B (j + 1) := by
  intro V
  dsimp [V]
  have h1 : B (j + 2) * Y j = Y j * B (j + 2) := (hYB_comm j (j + 2)).symm
  have h2 : B (j + 1) * Y j = Y j * B (j + 1) := (hYB_comm j (j + 1)).symm
  calc Y j * (X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)) +
       (X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)) * Y j
    _ = (Y j * X (j + 1)) * B (j + 2) + (Y j * X (j + 2)) * B (j + 1) +
        (X (j + 1) * (B (j + 2) * Y j) + X (j + 2) * (B (j + 1) * Y j)) := by noncomm_ring
    _ = (Y j * X (j + 1)) * B (j + 2) + (Y j * X (j + 2)) * B (j + 1) +
        (X (j + 1) * (Y j * B (j + 2)) + X (j + 2) * (Y j * B (j + 1))) := by rw [h1, h2]
    _ = (Y j * X (j + 1) + X (j + 1) * Y j) * B (j + 2) +
        (Y j * X (j + 2) + X (j + 2) * Y j) * B (j + 1) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_XW_add_WX {A : Type*} [Ring A] (X Y B : Fin 3 → A)
    (hXB_comm : ∀ j k, X j * B k = B k * X j)
    (j : Fin 3) :
    let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
    X j * W j + W j * X j =
      (X j * Y (j + 1) + Y (j + 1) * X j) * B (j + 2) +
      (X j * Y (j + 2) + Y (j + 2) * X j) * B (j + 1) := by
  intro W
  dsimp [W]
  have h1 : B (j + 2) * X j = X j * B (j + 2) := (hXB_comm j (j + 2)).symm
  have h2 : B (j + 1) * X j = X j * B (j + 1) := (hXB_comm j (j + 1)).symm
  calc X j * (Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)) +
       (Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)) * X j
    _ = (X j * Y (j + 1)) * B (j + 2) + (X j * Y (j + 2)) * B (j + 1) +
        (Y (j + 1) * (B (j + 2) * X j) + Y (j + 2) * (B (j + 1) * X j)) := by noncomm_ring
    _ = (X j * Y (j + 1)) * B (j + 2) + (X j * Y (j + 2)) * B (j + 1) +
        (Y (j + 1) * (X j * B (j + 2)) + Y (j + 2) * (X j * B (j + 1))) := by rw [h1, h2]
    _ = (X j * Y (j + 1) + Y (j + 1) * X j) * B (j + 2) +
        (X j * Y (j + 2) + Y (j + 2) * X j) * B (j + 1) := by noncomm_ring

lemma magic_rectangle_anticommutator_identities_VW_sq_add_sq {A : Type*} [Ring A]
    (Xi Xk Yi Yk Bi Bk Yj : A)
    (hBk_sq : Bk * Bk = 1)
    (hBi_sq : Bi * Bi = 1)
    (hXB_ik : Bk * Xi = Xi * Bk)
    (hXB_ki : Bi * Xk = Xk * Bi)
    (hXB_kk : Bk * Xk = Xk * Bk)
    (hXB_ii : Bi * Xi = Xi * Bi)
    (hYB_ik : Bk * Yi = Yi * Bk)
    (hYB_ki : Bi * Yk = Yk * Bi)
    (hYB_kk : Bk * Yk = Yk * Bk)
    (hYB_ii : Bi * Yi = Yi * Bi)
    (h_sq_i : Xi * Xi + Yi * Yi = 4)
    (h_sq_k : Xk * Xk + Yk * Yk = 4)
    (h_cr1 : Xi * Xk + Yi * Yk = 2 * Yj)
    (h_cr2 : Xk * Xi + Yk * Yi = 2 * Yj) :
    (Xi * Bk + Xk * Bi) ^ 2 + (Yi * Bk + Yk * Bi) ^ 2 =
      8 + 2 * Yj * (Bi * Bk + Bk * Bi) := by
  have h4 : (4 : A) + 4 = 8 := by norm_num
  rw [sq, sq]
  calc (Xi * Bk + Xk * Bi) * (Xi * Bk + Xk * Bi) + (Yi * Bk + Yk * Bi) * (Yi * Bk + Yk * Bi)
    _ = Xi * (Bk * Xi) * Bk + Xi * (Bk * Xk) * Bi + Xk * (Bi * Xi) * Bk + Xk * (Bi * Xk) * Bi +
        (Yi * (Bk * Yi) * Bk + Yi * (Bk * Yk) * Bi + Yk * (Bi * Yi) * Bk + Yk * (Bi * Yk) * Bi) := by noncomm_ring
    _ = Xi * (Xi * Bk) * Bk + Xi * (Xk * Bk) * Bi + Xk * (Xi * Bi) * Bk + Xk * (Xk * Bi) * Bi +
        (Yi * (Yi * Bk) * Bk + Yi * (Yk * Bk) * Bi + Yk * (Yi * Bi) * Bk + Yk * (Yk * Bi) * Bi) := by
        rw [hXB_ik, hXB_kk, hXB_ii, hXB_ki, hYB_ik, hYB_kk, hYB_ii, hYB_ki]
    _ = (Xi * Xi) * (Bk * Bk) + (Xk * Xk) * (Bi * Bi) + (Xi * Xk) * (Bk * Bi) + (Xk * Xi) * (Bi * Bk) +
        ((Yi * Yi) * (Bk * Bk) + (Yk * Yk) * (Bi * Bi) + (Yi * Yk) * (Bk * Bi) + (Yk * Yi) * (Bi * Bk)) := by noncomm_ring
    _ = (Xi * Xi) * 1 + (Xk * Xk) * 1 + (Xi * Xk) * (Bk * Bi) + (Xk * Xi) * (Bi * Bk) +
        ((Yi * Yi) * 1 + (Yk * Yk) * 1 + (Yi * Yk) * (Bk * Bi) + (Yk * Yi) * (Bi * Bk)) := by rw [hBk_sq, hBi_sq]
    _ = (Xi * Xi + Yi * Yi) + (Xk * Xk + Yk * Yk) + (Xi * Xk + Yi * Yk) * (Bk * Bi) + (Xk * Xi + Yk * Yi) * (Bi * Bk) := by noncomm_ring
    _ = 4 + 4 + (2 * Yj) * (Bk * Bi) + (2 * Yj) * (Bi * Bk) := by rw [h_sq_i, h_sq_k, h_cr1, h_cr2]
    _ = 8 + 2 * Yj * (Bi * Bk + Bk * Bi) := by rw [h4]; noncomm_ring

/-- Anticommutator identities for the magic rectangle certificate operators V and W in a ring. -/
theorem magic_rectangle_anticommutator_identities
    {A : Type*} [Ring A]
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
    let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
    let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
    let S := ∑ j : Fin 3, X j * B j
    let J := ∑ j : Fin 3, Y j * (B (j + 1) * B (j + 2) + B (j + 2) * B (j + 1))
    (∑ j : Fin 3, (V j ^ 2 + W j ^ 2) = 24 + 2 * J) ∧
    (∑ j : Fin 3, (W j * B j + B j * W j) = 2 * J) ∧
    (∑ j : Fin 3, (Y j * V j + V j * Y j) = 4 * S) ∧
    (∑ j : Fin 3, (X j * W j + W j * X j) = 4 * S) := by
  intro X Y V W S J
  have hXB (j k : Fin 3) : X j * B k = B k * X j :=
    magic_rectangle_anticommutator_identities_mul_XB_comm D C B hDB_comm hCB_comm j k
  have hYB (j k : Fin 3) : Y j * B k = B k * Y j :=
    magic_rectangle_anticommutator_identities_mul_YB_comm D C B hDB_comm hCB_comm j k
  have hB_sq_mul (m : Fin 3) : B m * B m = 1 := by rw [← sq, hB_sq]
  have h_sq0 : X 0 * X 0 + Y 0 * Y 0 = 4 := by
    have h := (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 0).1
    rw [← sq (X 0), ← sq (Y 0), h]
  have h_sq1 : X 1 * X 1 + Y 1 * Y 1 = 4 := by
    have h := (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 1).1
    rw [← sq (X 1), ← sq (Y 1), h]
  have h_sq2 : X 2 * X 2 + Y 2 * Y 2 = 4 := by
    have h := (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 2).1
    rw [← sq (X 2), ← sq (Y 2), h]
  have h_cr0 : X 1 * X 2 + Y 1 * Y 2 = 2 * Y 0 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 0).2.1
  have h_cr1 : X 2 * X 0 + Y 2 * Y 0 = 2 * Y 1 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 1).2.1
  have h_cr2 : X 0 * X 1 + Y 0 * Y 1 = 2 * Y 2 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 2).2.1
  have h_cr0_rev : X 2 * X 1 + Y 2 * Y 1 = 2 * Y 0 := by
    rw [magic_rectangle_anticommutator_identities_row_rel_rev1 D C hD_comm hC_comm 1 2, h_cr0]
  have h_cr1_rev : X 0 * X 2 + Y 0 * Y 2 = 2 * Y 1 := by
    rw [magic_rectangle_anticommutator_identities_row_rel_rev1 D C hD_comm hC_comm 2 0, h_cr1]
  have h_cr2_rev : X 1 * X 0 + Y 1 * Y 0 = 2 * Y 2 := by
    rw [magic_rectangle_anticommutator_identities_row_rel_rev1 D C hD_comm hC_comm 0 1, h_cr2]
  have hr0 : X 1 * Y 2 + Y 1 * X 2 = 2 * X 0 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 0).2.2
  have hr1 : X 2 * Y 0 + Y 2 * X 0 = 2 * X 1 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 1).2.2
  have hr2 : X 0 * Y 1 + Y 0 * X 1 = 2 * X 2 :=
    (magic_rectangle_row_relations D C hD_sq hC_sq hD_prod hC_prod hD_comm hC_comm 2).2.2
  have hrev0 : X 2 * Y 1 + Y 2 * X 1 = X 1 * Y 2 + Y 1 * X 2 :=
    magic_rectangle_anticommutator_identities_row_rel_rev2 D C hD_comm hC_comm 1 2
  have hrev1 : X 0 * Y 2 + Y 0 * X 2 = X 2 * Y 0 + Y 2 * X 0 :=
    magic_rectangle_anticommutator_identities_row_rel_rev2 D C hD_comm hC_comm 2 0
  have hrev2 : X 1 * Y 0 + Y 1 * X 0 = X 0 * Y 1 + Y 0 * X 1 :=
    magic_rectangle_anticommutator_identities_row_rel_rev2 D C hD_comm hC_comm 0 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1
    have hVW0 : V 0 ^ 2 + W 0 ^ 2 = 8 + 2 * Y 0 * (B 1 * B 2 + B 2 * B 1) := by
      change (X 1 * B 2 + X 2 * B 1) ^ 2 + (Y 1 * B 2 + Y 2 * B 1) ^ 2 = 8 + 2 * Y 0 * (B 1 * B 2 + B 2 * B 1)
      exact magic_rectangle_anticommutator_identities_VW_sq_add_sq (X 1) (X 2) (Y 1) (Y 2) (B 1) (B 2) (Y 0)
        (hB_sq_mul 2) (hB_sq_mul 1)
        (hXB 1 2).symm (hXB 2 1).symm (hXB 2 2).symm (hXB 1 1).symm
        (hYB 1 2).symm (hYB 2 1).symm (hYB 2 2).symm (hYB 1 1).symm
        h_sq1 h_sq2 h_cr0 h_cr0_rev
    have hVW1 : V 1 ^ 2 + W 1 ^ 2 = 8 + 2 * Y 1 * (B 2 * B 0 + B 0 * B 2) := by
      change (X 2 * B 0 + X 0 * B 2) ^ 2 + (Y 2 * B 0 + Y 0 * B 2) ^ 2 = 8 + 2 * Y 1 * (B 2 * B 0 + B 0 * B 2)
      exact magic_rectangle_anticommutator_identities_VW_sq_add_sq (X 2) (X 0) (Y 2) (Y 0) (B 2) (B 0) (Y 1)
        (hB_sq_mul 0) (hB_sq_mul 2)
        (hXB 2 0).symm (hXB 0 2).symm (hXB 0 0).symm (hXB 2 2).symm
        (hYB 2 0).symm (hYB 0 2).symm (hYB 0 0).symm (hYB 2 2).symm
        h_sq2 h_sq0 h_cr1 h_cr1_rev
    have hVW2 : V 2 ^ 2 + W 2 ^ 2 = 8 + 2 * Y 2 * (B 0 * B 1 + B 1 * B 0) := by
      change (X 0 * B 1 + X 1 * B 0) ^ 2 + (Y 0 * B 1 + Y 1 * B 0) ^ 2 = 8 + 2 * Y 2 * (B 0 * B 1 + B 1 * B 0)
      exact magic_rectangle_anticommutator_identities_VW_sq_add_sq (X 0) (X 1) (Y 0) (Y 1) (B 0) (B 1) (Y 2)
        (hB_sq_mul 1) (hB_sq_mul 0)
        (hXB 0 1).symm (hXB 1 0).symm (hXB 1 1).symm (hXB 0 0).symm
        (hYB 0 1).symm (hYB 1 0).symm (hYB 1 1).symm (hYB 0 0).symm
        h_sq0 h_sq1 h_cr2 h_cr2_rev
    dsimp [J]
    repeat rw [Fin.sum_univ_three]
    rw [magic_rectangle_anticommutator_identities_fin3_idx_01,
        magic_rectangle_anticommutator_identities_fin3_idx_02,
        magic_rectangle_anticommutator_identities_fin3_idx_11,
        magic_rectangle_anticommutator_identities_fin3_idx_12,
        magic_rectangle_anticommutator_identities_fin3_idx_21,
        magic_rectangle_anticommutator_identities_fin3_idx_22]
    rw [hVW0, hVW1, hVW2]
    have h24 : (8 : A) + 8 + 8 = 24 := by norm_num
    calc (8 + 2 * Y 0 * (B 1 * B 2 + B 2 * B 1)) +
         (8 + 2 * Y 1 * (B 2 * B 0 + B 0 * B 2)) +
         (8 + 2 * Y 2 * (B 0 * B 1 + B 1 * B 0))
      _ = (8 + 8 + 8) + 2 * (Y 0 * (B 1 * B 2 + B 2 * B 1) +
                             (Y 1 * (B 2 * B 0 + B 0 * B 2) +
                              Y 2 * (B 0 * B 1 + B 1 * B 0))) := by noncomm_ring
      _ = 24 + 2 * (Y 0 * (B 1 * B 2 + B 2 * B 1) +
                    Y 1 * (B 2 * B 0 + B 0 * B 2) +
                    Y 2 * (B 0 * B 1 + B 1 * B 0)) := by rw [h24]; noncomm_ring
  · -- Part 2
    dsimp [W, J]
    repeat rw [Fin.sum_univ_three]
    rw [magic_rectangle_anticommutator_identities_fin3_idx_01,
        magic_rectangle_anticommutator_identities_fin3_idx_02,
        magic_rectangle_anticommutator_identities_fin3_idx_11,
        magic_rectangle_anticommutator_identities_fin3_idx_12,
        magic_rectangle_anticommutator_identities_fin3_idx_21,
        magic_rectangle_anticommutator_identities_fin3_idx_22]
    simp only [mul_add, add_mul, magic_rectangle_anticommutator_identities_B_mul_Y_mul Y B hYB]
    noncomm_ring
  · -- Part 3
    dsimp [S]
    repeat rw [Fin.sum_univ_three]
    rw [magic_rectangle_anticommutator_identities_YV_add_VY X Y B hYB 0,
        magic_rectangle_anticommutator_identities_YV_add_VY X Y B hYB 1,
        magic_rectangle_anticommutator_identities_YV_add_VY X Y B hYB 2]
    rw [magic_rectangle_anticommutator_identities_fin3_idx_01,
        magic_rectangle_anticommutator_identities_fin3_idx_02,
        magic_rectangle_anticommutator_identities_fin3_idx_11,
        magic_rectangle_anticommutator_identities_fin3_idx_12,
        magic_rectangle_anticommutator_identities_fin3_idx_21,
        magic_rectangle_anticommutator_identities_fin3_idx_22]
    calc ((Y 0 * X 1 + X 1 * Y 0) * B 2 + (Y 0 * X 2 + X 2 * Y 0) * B 1) +
         ((Y 1 * X 2 + X 2 * Y 1) * B 0 + (Y 1 * X 0 + X 0 * Y 1) * B 2) +
         ((Y 2 * X 0 + X 0 * Y 2) * B 1 + (Y 2 * X 1 + X 1 * Y 2) * B 0)
      _ = ((X 1 * Y 2 + Y 1 * X 2) + (X 2 * Y 1 + Y 2 * X 1)) * B 0 +
          (((X 2 * Y 0 + Y 2 * X 0) + (X 0 * Y 2 + Y 0 * X 2)) * B 1 +
           ((X 0 * Y 1 + Y 0 * X 1) + (X 1 * Y 0 + Y 1 * X 0)) * B 2) := by noncomm_ring
      _ = (2 * X 0 + 2 * X 0) * B 0 +
          ((2 * X 1 + 2 * X 1) * B 1 +
           (2 * X 2 + 2 * X 2) * B 2) := by rw [hr0, hrev0, hr0, hr1, hrev1, hr1, hr2, hrev2, hr2]
      _ = 4 * (X 0 * B 0 + X 1 * B 1 + X 2 * B 2) := by noncomm_ring
  · -- Part 4
    dsimp [S]
    repeat rw [Fin.sum_univ_three]
    rw [magic_rectangle_anticommutator_identities_XW_add_WX X Y B hXB 0,
        magic_rectangle_anticommutator_identities_XW_add_WX X Y B hXB 1,
        magic_rectangle_anticommutator_identities_XW_add_WX X Y B hXB 2]
    rw [magic_rectangle_anticommutator_identities_fin3_idx_01,
        magic_rectangle_anticommutator_identities_fin3_idx_02,
        magic_rectangle_anticommutator_identities_fin3_idx_11,
        magic_rectangle_anticommutator_identities_fin3_idx_12,
        magic_rectangle_anticommutator_identities_fin3_idx_21,
        magic_rectangle_anticommutator_identities_fin3_idx_22]
    calc ((X 0 * Y 1 + Y 1 * X 0) * B 2 + (X 0 * Y 2 + Y 2 * X 0) * B 1) +
         ((X 1 * Y 2 + Y 2 * X 1) * B 0 + (X 1 * Y 0 + Y 0 * X 1) * B 2) +
         ((X 2 * Y 0 + Y 0 * X 2) * B 1 + (X 2 * Y 1 + Y 1 * X 2) * B 0)
      _ = ((X 1 * Y 2 + Y 1 * X 2) + (X 2 * Y 1 + Y 2 * X 1)) * B 0 +
          (((X 2 * Y 0 + Y 2 * X 0) + (X 0 * Y 2 + Y 0 * X 2)) * B 1 +
           ((X 0 * Y 1 + Y 0 * X 1) + (X 1 * Y 0 + Y 1 * X 0)) * B 2) := by noncomm_ring
      _ = (2 * X 0 + 2 * X 0) * B 0 +
          ((2 * X 1 + 2 * X 1) * B 1 +
           (2 * X 2 + 2 * X 2) * B 2) := by rw [hr0, hrev0, hr0, hr1, hrev1, hr1, hr2, hrev2, hr2]
      _ = 4 * (X 0 * B 0 + X 1 * B 1 + X 2 * B 2) := by noncomm_ring
