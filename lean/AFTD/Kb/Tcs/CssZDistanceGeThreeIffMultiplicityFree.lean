import AFTD.Prelude

/-!
# css_z_distance_ge_three_iff_multiplicity_free

Topic: quantum   Node: c8473f069bb3

Provenance: formalization of a published result. Source: arXiv:2610.09341 (Building codes with transversal CCZ using projective geometry), Lemma 2.1; the multiplicity-free condition is stated in its contrapositive form (equal syndromes force equal labels).

For binary matrices K (k × n) and S (s × n), the CSS code with generator matrix [K; S] has Z-distance at least 3 (every v ∈ F_2^n with Sv = 0 and Kv ≠ 0 has Hamming weight ≥ 3) if and only if its columns (α_j, β_j) = (K e_j, S e_j) are multiplicity-free: no column has β_j = 0 with α_j ≠ 0, and no two distinct columns have β_i = β_j with α_i ≠ α_j.
-/

lemma css_z_distance_ge_three_iff_multiplicity_free_zmod2_ne_zero {x : ZMod 2} :
    x ≠ 0 ↔ x = 1 := by
  revert x; decide

lemma css_z_distance_ge_three_iff_multiplicity_free_zmod2_add_eq_zero {x y : ZMod 2} :
    x + y = 0 ↔ x = y := by
  revert x y; decide

lemma css_z_distance_ge_three_iff_multiplicity_free_zmod2_vec_add_eq_zero
    {m : Type*} (u v : m → ZMod 2) : u + v = 0 ↔ u = v := by
  simp [funext_iff, css_z_distance_ge_three_iff_multiplicity_free_zmod2_add_eq_zero]

lemma css_z_distance_ge_three_iff_multiplicity_free_vec_eq_zero_of_support_empty
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → ZMod 2)
    (h : (Finset.univ.filter (fun j => v j ≠ 0)) = ∅) : v = 0 := by
  ext x
  have : x ∉ Finset.univ.filter (fun j => v j ≠ 0) := by simp [h]
  simp at this
  exact this

lemma css_z_distance_ge_three_iff_multiplicity_free_vec_eq_single_of_support_singleton
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → ZMod 2)
    {j : n} (h : (Finset.univ.filter (fun x => v x ≠ 0)) = {j}) :
    v = Pi.single j 1 := by
  have hj : v j ≠ 0 := by
    have : j ∈ Finset.univ.filter (fun x => v x ≠ 0) := by rw [h]; exact Finset.mem_singleton_self j
    simp at this
    exact this
  ext x
  by_cases hx : x = j
  · subst hx
    rw [css_z_distance_ge_three_iff_multiplicity_free_zmod2_ne_zero.mp hj, Pi.single_eq_same]
  · have : x ∉ Finset.univ.filter (fun x => v x ≠ 0) := by
      rw [h]
      simp [hx]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
    rw [this, Pi.single_eq_of_ne hx]

lemma css_z_distance_ge_three_iff_multiplicity_free_vec_eq_add_of_support_pair
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → ZMod 2)
    {i j : n} (hij : i ≠ j) (h : (Finset.univ.filter (fun x => v x ≠ 0)) = {i, j}) :
    v = Pi.single i 1 + Pi.single j 1 := by
  have hi : v i ≠ 0 := by
    have : i ∈ Finset.univ.filter (fun x => v x ≠ 0) := by rw [h]; exact Finset.mem_insert_self i _
    simp at this
    exact this
  have hj : v j ≠ 0 := by
    have : j ∈ Finset.univ.filter (fun x => v x ≠ 0) := by rw [h]; simp
    simp at this
    exact this
  ext x
  by_cases hxi : x = i
  · subst hxi
    rw [css_z_distance_ge_three_iff_multiplicity_free_zmod2_ne_zero.mp hi, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
  · by_cases hxj : x = j
    · subst hxj
      rw [css_z_distance_ge_three_iff_multiplicity_free_zmod2_ne_zero.mp hj, Pi.add_apply, Pi.single_eq_of_ne hxi, Pi.single_eq_same, zero_add]
    · have : x ∉ Finset.univ.filter (fun x => v x ≠ 0) := by
        rw [h]
        simp [hxi, hxj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
      rw [this, Pi.add_apply, Pi.single_eq_of_ne hxi, Pi.single_eq_of_ne hxj, add_zero]

lemma css_z_distance_ge_three_iff_multiplicity_free_support_single
    {n : Type*} [Fintype n] [DecidableEq n] (j : n) :
    (Finset.univ.filter (fun x => (Pi.single j 1 : n → ZMod 2) x ≠ 0)).card = 1 := by
  have : (Finset.univ.filter (fun x => (Pi.single j 1 : n → ZMod 2) x ≠ 0)) = {j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    simp only [Pi.single_apply]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [this, Finset.card_singleton]

lemma css_z_distance_ge_three_iff_multiplicity_free_support_single_add_single
    {n : Type*} [Fintype n] [DecidableEq n] {i j : n} (hij : i ≠ j) :
    let v : n → ZMod 2 := Pi.single i 1 + Pi.single j 1
    (Finset.univ.filter (fun x => v x ≠ 0)).card = 2 := by
  intro v
  have : (Finset.univ.filter (fun x => v x ≠ 0)) = {i, j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    simp only [v, Pi.add_apply, Pi.single_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    · simp [hxi]
  rw [this, Finset.card_pair hij]

theorem css_z_distance_ge_three_iff_multiplicity_free {k s n : ℕ}
    (K : Matrix (Fin k) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2)) :
    (∀ v : Fin n → ZMod 2, Matrix.mulVec S v = 0 → Matrix.mulVec K v ≠ 0 →
        3 ≤ (Finset.univ.filter (fun j => v j ≠ 0)).card) ↔
      ((∀ j, S.transpose j = 0 → K.transpose j = 0) ∧
        (∀ i j, i ≠ j → S.transpose i = S.transpose j → K.transpose i = K.transpose j)) := by
  constructor
  · intro h_dist
    refine ⟨fun j hj => ?_, fun i j hij hij_S => ?_⟩
    · by_contra hk
      have hSv : Matrix.mulVec S (Pi.single j 1) = 0 := by
        rw [Matrix.mulVec_single_one]; exact hj
      have hKv : Matrix.mulVec K (Pi.single j 1) ≠ 0 := by
        rw [Matrix.mulVec_single_one]; exact hk
      have hcard := h_dist (Pi.single j 1) hSv hKv
      rw [css_z_distance_ge_three_iff_multiplicity_free_support_single j] at hcard
      omega
    · by_contra hij_K
      let v : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1
      have hSv : Matrix.mulVec S v = 0 := by
        change Matrix.mulVec S (Pi.single i 1 + Pi.single j 1) = 0
        rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
        exact (css_z_distance_ge_three_iff_multiplicity_free_zmod2_vec_add_eq_zero _ _).mpr hij_S
      have hKv : Matrix.mulVec K v ≠ 0 := by
        change Matrix.mulVec K (Pi.single i 1 + Pi.single j 1) ≠ 0
        rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
        intro h
        exact hij_K ((css_z_distance_ge_three_iff_multiplicity_free_zmod2_vec_add_eq_zero _ _).mp h)
      have hcard := h_dist v hSv hKv
      have hcard2 : (Finset.univ.filter (fun x => v x ≠ 0)).card = 2 :=
        css_z_distance_ge_three_iff_multiplicity_free_support_single_add_single hij
      rw [hcard2] at hcard
      omega
  · rintro ⟨h1, h2⟩ v hSv hKv
    by_contra! hc
    have hcases : (Finset.univ.filter (fun j => v j ≠ 0)).card = 0 ∨
        (Finset.univ.filter (fun j => v j ≠ 0)).card = 1 ∨
        (Finset.univ.filter (fun j => v j ≠ 0)).card = 2 := by omega
    rcases hcases with hc0 | hc1 | hc2
    · rw [Finset.card_eq_zero] at hc0
      have hv0 : v = 0 :=
        css_z_distance_ge_three_iff_multiplicity_free_vec_eq_zero_of_support_empty v hc0
      subst hv0
      rw [Matrix.mulVec_zero] at hKv
      exact hKv rfl
    · rw [Finset.card_eq_one] at hc1
      obtain ⟨j, hj⟩ := hc1
      have hv : v = Pi.single j 1 :=
        css_z_distance_ge_three_iff_multiplicity_free_vec_eq_single_of_support_singleton v hj
      subst hv
      have hSj : S.transpose j = 0 := by
        have : Matrix.mulVec S (Pi.single j 1) = S.transpose j := by
          rw [Matrix.mulVec_single_one]; rfl
        rwa [this] at hSv
      have hKj := h1 j hSj
      have : Matrix.mulVec K (Pi.single j 1) = K.transpose j := by
        rw [Matrix.mulVec_single_one]; rfl
      rw [this, hKj] at hKv
      exact hKv rfl
    · rw [Finset.card_eq_two] at hc2
      obtain ⟨i, j, hij, hij_supp⟩ := hc2
      have hv : v = Pi.single i 1 + Pi.single j 1 :=
        css_z_distance_ge_three_iff_multiplicity_free_vec_eq_add_of_support_pair v hij hij_supp
      subst hv
      have hSij : S.transpose i = S.transpose j := by
        have : Matrix.mulVec S (Pi.single i 1 + Pi.single j 1) = S.transpose i + S.transpose j := by
          rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]; rfl
        have h0 : S.transpose i + S.transpose j = 0 := by rwa [this] at hSv
        exact (css_z_distance_ge_three_iff_multiplicity_free_zmod2_vec_add_eq_zero _ _).mp h0
      have hKij := h2 i j hij hSij
      have : Matrix.mulVec K (Pi.single i 1 + Pi.single j 1) = K.transpose i + K.transpose j := by
        rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]; rfl
      have h0 : K.transpose i + K.transpose j = 0 :=
        (css_z_distance_ge_three_iff_multiplicity_free_zmod2_vec_add_eq_zero _ _).mpr hKij
      rw [this, h0] at hKv
      exact hKv rfl
