import AFTD.Prelude

/-!
# magic_rectangle_row_relations

Topic: quantum   Node: b33a50dc2914

Provenance: helper lemma. arXiv:2610.12001, Eq. (11)

Let A be a ring and let D, C : Fin 3 → A satisfy D j ^ 2 = 1 and C j ^ 2 = 1 for all j, D 0 * D 1 * D 2 = 1, C 0 * C 1 * C 2 = -1, and pairwise commutativity D j * D k = D k * D j and C j * C k = C k * C j for all j, k. Setting X m = D m + C m and Y m = D m - C m, for every j : Fin 3 with i = j + 1 and k = j + 2, we have X j ^ 2 + Y j ^ 2 = 4, X i * X k + Y i * Y k = 2 * Y j, and X i * Y k + Y i * X k = 2 * X j.
-/

lemma magic_rectangle_row_relations_sq_eq_mul
    {A : Type*} [Ring A] (x : A) (h : x ^ 2 = 1) : x * x = 1 := by
  rwa [sq] at h

lemma magic_rectangle_row_relations_sq_add_sq
    {A : Type*} [Ring A] (x y : A) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    (x + y) ^ 2 + (x - y) ^ 2 = 4 := by
  have h : (x + y) ^ 2 + (x - y) ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 := by noncomm_ring
  rw [h, hx, hy]
  norm_num

lemma magic_rectangle_row_relations_cross_sum
    {A : Type*} [Ring A] (d1 d2 c1 c2 dj cj : A)
    (hd : d1 * d2 = dj) (hc : c1 * c2 = - cj) :
    (d1 + c1) * (d2 + c2) + (d1 - c1) * (d2 - c2) = 2 * (dj - cj) := by
  calc (d1 + c1) * (d2 + c2) + (d1 - c1) * (d2 - c2)
    _ = 2 * (d1 * d2 + c1 * c2) := by noncomm_ring
    _ = 2 * (dj + - cj) := by rw [hd, hc]
    _ = 2 * (dj - cj) := by noncomm_ring

lemma magic_rectangle_row_relations_cross_diff
    {A : Type*} [Ring A] (d1 d2 c1 c2 dj cj : A)
    (hd : d1 * d2 = dj) (hc : c1 * c2 = - cj) :
    (d1 + c1) * (d2 - c2) + (d1 - c1) * (d2 + c2) = 2 * (dj + cj) := by
  calc (d1 + c1) * (d2 - c2) + (d1 - c1) * (d2 + c2)
    _ = 2 * (d1 * d2 - c1 * c2) := by noncomm_ring
    _ = 2 * (dj - - cj) := by rw [hd, hc]
    _ = 2 * (dj + cj) := by noncomm_ring

/-- Row parity relations and anticommutation identities for X_j and Y_j in a ring. -/
theorem magic_rectangle_row_relations
    {A : Type*} [Ring A]
    (D C : Fin 3 → A)
    (hD_sq : ∀ j, D j ^ 2 = 1)
    (hC_sq : ∀ j, C j ^ 2 = 1)
    (hD_prod : D 0 * D 1 * D 2 = 1)
    (hC_prod : C 0 * C 1 * C 2 = -1)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (j : Fin 3) :
    let X := fun m => D m + C m
    let Y := fun m => D m - C m
    let i := j + 1
    let k := j + 2
    X j ^ 2 + Y j ^ 2 = 4 ∧
    X i * X k + Y i * Y k = 2 * Y j ∧
    X i * Y k + Y i * X k = 2 * X j := by
  have hD_sq_mul (m : Fin 3) : D m * D m = 1 :=
    magic_rectangle_row_relations_sq_eq_mul (D m) (hD_sq m)
  have hC_sq_mul (m : Fin 3) : C m * C m = 1 :=
    magic_rectangle_row_relations_sq_eq_mul (C m) (hC_sq m)
  have hD01 : D 0 * D 1 = D 2 := by
    calc D 0 * D 1 = (D 0 * D 1) * 1 := by noncomm_ring
    _ = (D 0 * D 1) * (D 2 * D 2) := by rw [hD_sq_mul 2]
    _ = (D 0 * D 1 * D 2) * D 2 := by noncomm_ring
    _ = 1 * D 2 := by rw [hD_prod]
    _ = D 2 := by noncomm_ring
  have hD12 : D 1 * D 2 = D 0 := by
    calc D 1 * D 2 = 1 * (D 1 * D 2) := by noncomm_ring
    _ = (D 0 * D 0) * (D 1 * D 2) := by rw [hD_sq_mul 0]
    _ = D 0 * (D 0 * D 1 * D 2) := by noncomm_ring
    _ = D 0 * 1 := by rw [hD_prod]
    _ = D 0 := by noncomm_ring
  have hD20 : D 2 * D 0 = D 1 := by
    calc D 2 * D 0 = 1 * (D 2 * D 0) := by noncomm_ring
    _ = (D 1 * D 1) * (D 2 * D 0) := by rw [hD_sq_mul 1]
    _ = D 1 * (D 1 * (D 2 * D 0)) := by noncomm_ring
    _ = D 1 * (D 1 * (D 0 * D 2)) := by rw [hD_comm 2 0]
    _ = D 1 * ((D 1 * D 0) * D 2) := by noncomm_ring
    _ = D 1 * ((D 0 * D 1) * D 2) := by rw [hD_comm 1 0]
    _ = D 1 * (D 0 * D 1 * D 2) := by noncomm_ring
    _ = D 1 * 1 := by rw [hD_prod]
    _ = D 1 := by noncomm_ring
  have hC01 : C 0 * C 1 = - C 2 := by
    calc C 0 * C 1 = (C 0 * C 1) * 1 := by noncomm_ring
    _ = (C 0 * C 1) * (C 2 * C 2) := by rw [hC_sq_mul 2]
    _ = (C 0 * C 1 * C 2) * C 2 := by noncomm_ring
    _ = -1 * C 2 := by rw [hC_prod]
    _ = - C 2 := by noncomm_ring
  have hC12 : C 1 * C 2 = - C 0 := by
    calc C 1 * C 2 = 1 * (C 1 * C 2) := by noncomm_ring
    _ = (C 0 * C 0) * (C 1 * C 2) := by rw [hC_sq_mul 0]
    _ = C 0 * (C 0 * C 1 * C 2) := by noncomm_ring
    _ = C 0 * (-1) := by rw [hC_prod]
    _ = - C 0 := by noncomm_ring
  have hC20 : C 2 * C 0 = - C 1 := by
    calc C 2 * C 0 = 1 * (C 2 * C 0) := by noncomm_ring
    _ = (C 1 * C 1) * (C 2 * C 0) := by rw [hC_sq_mul 1]
    _ = C 1 * (C 1 * (C 2 * C 0)) := by noncomm_ring
    _ = C 1 * (C 1 * (C 0 * C 2)) := by rw [hC_comm 2 0]
    _ = C 1 * ((C 1 * C 0) * C 2) := by noncomm_ring
    _ = C 1 * ((C 0 * C 1) * C 2) := by rw [hC_comm 1 0]
    _ = C 1 * (C 0 * C 1 * C 2) := by noncomm_ring
    _ = C 1 * (-1) := by rw [hC_prod]
    _ = - C 1 := by noncomm_ring
  intro X Y i k
  fin_cases j
  · change (D 0 + C 0) ^ 2 + (D 0 - C 0) ^ 2 = 4 ∧
      (D 1 + C 1) * (D 2 + C 2) + (D 1 - C 1) * (D 2 - C 2) = 2 * (D 0 - C 0) ∧
      (D 1 + C 1) * (D 2 - C 2) + (D 1 - C 1) * (D 2 + C 2) = 2 * (D 0 + C 0)
    exact ⟨magic_rectangle_row_relations_sq_add_sq (D 0) (C 0) (hD_sq 0) (hC_sq 0),
           magic_rectangle_row_relations_cross_sum (D 1) (D 2) (C 1) (C 2) (D 0) (C 0) hD12 hC12,
           magic_rectangle_row_relations_cross_diff (D 1) (D 2) (C 1) (C 2) (D 0) (C 0) hD12 hC12⟩
  · change (D 1 + C 1) ^ 2 + (D 1 - C 1) ^ 2 = 4 ∧
      (D 2 + C 2) * (D 0 + C 0) + (D 2 - C 2) * (D 0 - C 0) = 2 * (D 1 - C 1) ∧
      (D 2 + C 2) * (D 0 - C 0) + (D 2 - C 2) * (D 0 + C 0) = 2 * (D 1 + C 1)
    exact ⟨magic_rectangle_row_relations_sq_add_sq (D 1) (C 1) (hD_sq 1) (hC_sq 1),
           magic_rectangle_row_relations_cross_sum (D 2) (D 0) (C 2) (C 0) (D 1) (C 1) hD20 hC20,
           magic_rectangle_row_relations_cross_diff (D 2) (D 0) (C 2) (C 0) (D 1) (C 1) hD20 hC20⟩
  · change (D 2 + C 2) ^ 2 + (D 2 - C 2) ^ 2 = 4 ∧
      (D 0 + C 0) * (D 1 + C 1) + (D 0 - C 0) * (D 1 - C 1) = 2 * (D 2 - C 2) ∧
      (D 0 + C 0) * (D 1 - C 1) + (D 0 - C 0) * (D 1 + C 1) = 2 * (D 2 + C 2)
    exact ⟨magic_rectangle_row_relations_sq_add_sq (D 2) (C 2) (hD_sq 2) (hC_sq 2),
           magic_rectangle_row_relations_cross_sum (D 0) (D 1) (C 0) (C 1) (D 2) (C 2) hD01 hC01,
           magic_rectangle_row_relations_cross_diff (D 0) (D 1) (C 0) (C 1) (D 2) (C 2) hD01 hC01⟩
