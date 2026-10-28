import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# four_point_primitive_boundary_kernel_is_atom

Topic: elementary_number_theory   Node: f812f6530314

Provenance: helper lemma. Standard supporting linear-algebra and divisibility step for OP-197 / arXiv:2610.16562 Conjecture1. Not claimed novel or research-level.

For a rank-two integer matrix on four columns that has a strictly positive common kernel vector, every nonzero nonnegative primitive integer kernel vector with a zero coordinate is an atom of its nonnegative integer kernel.
-/

set_option linter.unusedVariables false

lemma four_point_primitive_boundary_kernel_is_atom_helper_prop {ι : Type*} (u y : ι → ℤ)
    (hu0 : ∀ i, 0 ≤ u i) (hun : u ≠ 0)
    (hy0 : ∀ i, 0 ≤ y i) (hyu : ∀ i, y i ≤ u i)
    (hprop : ∀ i j, u i * y j = u j * y i)
    (hprim : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ u i) → d ∣ 1) :
    y = 0 ∨ y = u := by
  have ⟨j, hj⟩ : ∃ j, 0 < u j := by
    by_contra! h
    apply hun
    funext i
    have : 0 ≤ u i := hu0 i
    have : u i ≤ 0 := h i
    change u i = 0
    omega
  have hjy : 0 ≤ y j := hy0 j
  have hjyu : y j ≤ u j := hyu j
  let D : ℕ := (u j).natAbs
  let b : ℕ := (y j).natAbs
  have hD : (D : ℤ) = u j := Int.natAbs_of_nonneg (by omega)
  have hb : (b : ℤ) = y j := Int.natAbs_of_nonneg hjy
  have hDpos : 0 < D := by omega
  have hbD : b ≤ D := by omega
  let g : ℕ := D.gcd b
  let D' : ℕ := D / g
  let b' : ℕ := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b hDpos
  have hcop : Nat.Coprime D' b' := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b hDpos)
  have hrel : ∀ i, (D' : ℤ) * y i = (b' : ℤ) * u i := by
    intro i
    have he := hprop i j
    rw [← hD, ← hb] at he
    have he2 : ((D : ℤ) * y i) = ((b : ℤ) * u i) := by linarith
    have hDg : (D : ℤ) = (g : ℤ) * (D' : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left D b)).symm
    have hbg : (b : ℤ) = (g : ℤ) * (b' : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right D b)).symm
    rw [hDg, hbg] at he2
    have hgz : (g : ℤ) ≠ 0 := by omega
    nlinarith
  have hdvd : ∀ i, (D' : ℤ) ∣ u i := by
    intro i
    have h1 : (D' : ℤ) ∣ (b' : ℤ) * u i := by
      use y i
      rw [hrel i]
    have hgcd : Int.gcd (D' : ℤ) (b' : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact hcop
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h1 hgcd
  have hD'1 : D' ∣ 1 := hprim D' hdvd
  have hD'eq : D' = 1 := Nat.dvd_one.mp hD'1
  have hgD : g = D := by
    have : D = g * D' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left D b)).symm
    rw [hD'eq, mul_one] at this
    exact this.symm
  have hDb : D ∣ b := by
    rw [← hgD]
    exact Nat.gcd_dvd_right D b
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · left
    funext i
    have hr := hrel i
    have hb'0 : (b' : ℤ) = 0 := by
      dsimp [b']
      rw [hb0]
      simp
    rw [hb'0, zero_mul, hD'eq, Nat.cast_one, one_mul] at hr
    exact hr
  · right
    have hbD_eq : b = D := by
      rcases hDb with ⟨k, hk⟩
      have : k = 1 := by
        have : k ≠ 0 := by rintro rfl; omega
        nlinarith
      rw [hk, this, mul_one]
    funext i
    have hr := hrel i
    have hb'eq : b' = 1 := by
      dsimp [b']
      rw [hbD_eq, ← hgD, Nat.div_self hgpos]
    rw [hD'eq, hb'eq, Nat.cast_one, one_mul, one_mul] at hr
    exact hr

lemma four_point_primitive_boundary_kernel_is_atom_helper_3
    (a0 a1 a2 b0 b1 b2 u0 u1 u2 y0 y1 y2 : ℤ)
    (hua : u0 * a0 + u1 * a1 + u2 * a2 = 0)
    (hub : u0 * b0 + u1 * b1 + u2 * b2 = 0)
    (hya : y0 * a0 + y1 * a1 + y2 * a2 = 0)
    (hyb : y0 * b0 + y1 * b1 + y2 * b2 = 0)
    (hind : a0 * b1 - a1 * b0 ≠ 0) :
    u0 * y1 = u1 * y0 ∧ u0 * y2 = u2 * y0 ∧ u1 * y2 = u2 * y1 := by
  let M := a0 * b1 - a1 * b0
  let C0 := a1 * b2 - a2 * b1
  let C1 := a2 * b0 - a0 * b2
  have hu0 : u0 * M = u2 * C0 := by
    calc u0 * M
      _ = u0 * (a0 * b1 - a1 * b0) - b1 * (u0 * a0 + u1 * a1 + u2 * a2) + a1 * (u0 * b0 + u1 * b1 + u2 * b2) := by
        rw [hua, hub]; ring
      _ = u2 * C0 := by ring
  have hu1 : u1 * M = u2 * C1 := by
    calc u1 * M
      _ = u1 * (a0 * b1 - a1 * b0) + b0 * (u0 * a0 + u1 * a1 + u2 * a2) - a0 * (u0 * b0 + u1 * b1 + u2 * b2) := by
        rw [hua, hub]; ring
      _ = u2 * C1 := by ring
  have hy0 : y0 * M = y2 * C0 := by
    calc y0 * M
      _ = y0 * (a0 * b1 - a1 * b0) - b1 * (y0 * a0 + y1 * a1 + y2 * a2) + a1 * (y0 * b0 + y1 * b1 + y2 * b2) := by
        rw [hya, hyb]; ring
      _ = y2 * C0 := by ring
  have hy1 : y1 * M = y2 * C1 := by
    calc y1 * M
      _ = y1 * (a0 * b1 - a1 * b0) + b0 * (y0 * a0 + y1 * a1 + y2 * a2) - a0 * (y0 * b0 + y1 * b1 + y2 * b2) := by
        rw [hya, hyb]; ring
      _ = y2 * C1 := by ring
  have hM2 : M * M ≠ 0 := mul_ne_zero hind hind
  refine ⟨?_, ?_, ?_⟩
  · have h : M * M * (u0 * y1) = M * M * (u1 * y0) := by
      calc M * M * (u0 * y1)
        _ = (u0 * M) * (y1 * M) := by ring
        _ = (u2 * C0) * (y2 * C1) := by rw [hu0, hy1]
        _ = (u1 * M) * (y0 * M) := by
          have : (u2 * C0) * (y2 * C1) = (u2 * C1) * (y2 * C0) := by ring
          rw [this, ← hu1, ← hy0]
        _ = M * M * (u1 * y0) := by ring
    exact mul_left_cancel₀ hM2 h
  · have h : M * (u0 * y2) = M * (u2 * y0) := by
      calc M * (u0 * y2)
        _ = (u0 * M) * y2 := by ring
        _ = (u2 * C0) * y2 := by rw [hu0]
        _ = (y2 * C0) * u2 := by ring
        _ = (y0 * M) * u2 := by rw [← hy0]
        _ = M * (u2 * y0) := by ring
    exact mul_left_cancel₀ hind h
  · have h : M * (u1 * y2) = M * (u2 * y1) := by
      calc M * (u1 * y2)
        _ = (u1 * M) * y2 := by ring
        _ = (u2 * C1) * y2 := by rw [hu1]
        _ = (y2 * C1) * u2 := by ring
        _ = (y1 * M) * u2 := by rw [← hy1]
        _ = M * (u2 * y1) := by ring
    exact mul_left_cancel₀ hind h

lemma four_point_primitive_boundary_kernel_is_atom_helper_x0 (a b x : Fin 4 → ℤ)
    (hxa : (∑ i, x i * a i) = 0) (hxb : (∑ i, x i * b i) = 0) :
    x 0 * (a 0 * b 1 - a 1 * b 0) =
      x 2 * (a 1 * b 2 - a 2 * b 1) + x 3 * (a 1 * b 3 - a 3 * b 1) := by
  have ha : x 0 * a 0 + x 1 * a 1 + x 2 * a 2 + x 3 * a 3 = 0 := by
    have := hxa; simp only [Fin.sum_univ_four] at this; linarith
  have hb : x 0 * b 0 + x 1 * b 1 + x 2 * b 2 + x 3 * b 3 = 0 := by
    have := hxb; simp only [Fin.sum_univ_four] at this; linarith
  calc x 0 * (a 0 * b 1 - a 1 * b 0)
    _ = x 0 * (a 0 * b 1 - a 1 * b 0) - b 1 * (x 0 * a 0 + x 1 * a 1 + x 2 * a 2 + x 3 * a 3)
        + a 1 * (x 0 * b 0 + x 1 * b 1 + x 2 * b 2 + x 3 * b 3) := by
      rw [ha, hb]; ring
    _ = x 2 * (a 1 * b 2 - a 2 * b 1) + x 3 * (a 1 * b 3 - a 3 * b 1) := by ring

lemma four_point_primitive_boundary_kernel_is_atom_helper_x1 (a b x : Fin 4 → ℤ)
    (hxa : (∑ i, x i * a i) = 0) (hxb : (∑ i, x i * b i) = 0) :
    x 1 * (a 0 * b 1 - a 1 * b 0) =
      - x 2 * (a 0 * b 2 - a 2 * b 0) - x 3 * (a 0 * b 3 - a 3 * b 0) := by
  have ha : x 0 * a 0 + x 1 * a 1 + x 2 * a 2 + x 3 * a 3 = 0 := by
    have := hxa; simp only [Fin.sum_univ_four] at this; linarith
  have hb : x 0 * b 0 + x 1 * b 1 + x 2 * b 2 + x 3 * b 3 = 0 := by
    have := hxb; simp only [Fin.sum_univ_four] at this; linarith
  calc x 1 * (a 0 * b 1 - a 1 * b 0)
    _ = x 1 * (a 0 * b 1 - a 1 * b 0) + b 0 * (x 0 * a 0 + x 1 * a 1 + x 2 * a 2 + x 3 * a 3)
        - a 0 * (x 0 * b 0 + x 1 * b 1 + x 2 * b 2 + x 3 * b 3) := by
      rw [ha, hb]; ring
    _ = - x 2 * (a 0 * b 2 - a 2 * b 0) - x 3 * (a 0 * b 3 - a 3 * b 0) := by ring

theorem four_point_primitive_boundary_kernel_is_atom
    (a b x u : Fin 4 → ℤ) (hx : ∀ i, 0 < x i)
    (hxa : (∑ i, x i*a i) = 0) (hxb : (∑ i, x i*b i) = 0)
    (hind : a 0*b 1-a 1*b 0 ≠ 0)
    (hu : ∀ i, 0 ≤ u i) (hun : u ≠ 0)
    (hua : (∑ i, u i*a i) = 0) (hub : (∑ i, u i*b i) = 0)
    (hboundary : ∃ i, u i=0)
    (hprimitive : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ u i) → d ∣ 1) :
    ∀ y : Fin 4 → ℤ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ u i) →
      (∑ i, y i*a i) = 0 → (∑ i, y i*b i) = 0 → y=0 ∨ y=u := by
  intro y hy0 hyu hya hyb
  obtain ⟨k, hk⟩ := hboundary
  have hyk : y k = 0 := by
    have := hy0 k; have := hyu k; rw [hk] at this; omega
  have hprop : ∀ i j, u i * y j = u j * y i := by
    fin_cases k
    · -- k = 0: u 0 = 0, y 0 = 0
      have hu0 : u 0 = 0 := hk
      have hy0 : y 0 = 0 := hyk
      have hua' : u 1 * a 1 + u 2 * a 2 + u 3 * a 3 = 0 := by
        have := hua; simp only [Fin.sum_univ_four] at this; rw [hu0] at this; linarith
      have hub' : u 1 * b 1 + u 2 * b 2 + u 3 * b 3 = 0 := by
        have := hub; simp only [Fin.sum_univ_four] at this; rw [hu0] at this; linarith
      have hya' : y 1 * a 1 + y 2 * a 2 + y 3 * a 3 = 0 := by
        have := hya; simp only [Fin.sum_univ_four] at this; rw [hy0] at this; linarith
      have hyb' : y 1 * b 1 + y 2 * b 2 + y 3 * b 3 = 0 := by
        have := hyb; simp only [Fin.sum_univ_four] at this; rw [hy0] at this; linarith
      have hminors : a 1 * b 2 - a 2 * b 1 ≠ 0 ∨ a 1 * b 3 - a 3 * b 1 ≠ 0 := by
        by_contra! h
        rcases h with ⟨h12, h13⟩
        have hid := four_point_primitive_boundary_kernel_is_atom_helper_x0 a b x hxa hxb
        rw [h12, h13] at hid
        have hid2 : x 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by linarith
        have hx0 : x 0 ≠ 0 := (hx 0).ne'
        have : a 0 * b 1 - a 1 * b 0 = 0 := by
          cases mul_eq_zero.mp hid2 with
          | inl h => exact False.elim (hx0 h)
          | inr h => exact h
        exact hind this
      rcases hminors with h12ne | h13ne
      · have ⟨h12, h13, h23⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
          (a 1) (a 2) (a 3) (b 1) (b 2) (b 3) (u 1) (u 2) (u 3) (y 1) (y 2) (y 3)
          hua' hub' hya' hyb' h12ne
        intro i j
        fin_cases i <;> fin_cases j <;> dsimp <;>
          first
          | rfl
          | exact h12 | exact h12.symm
          | exact h13 | exact h13.symm
          | exact h23 | exact h23.symm
          | (rw [hu0, hy0]; ring)
      · have hua'' : u 1 * a 1 + u 3 * a 3 + u 2 * a 2 = 0 := by linarith
        have hub'' : u 1 * b 1 + u 3 * b 3 + u 2 * b 2 = 0 := by linarith
        have hya'' : y 1 * a 1 + y 3 * a 3 + y 2 * a 2 = 0 := by linarith
        have hyb'' : y 1 * b 1 + y 3 * b 3 + y 2 * b 2 = 0 := by linarith
        have ⟨h13, h12, h32⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
          (a 1) (a 3) (a 2) (b 1) (b 3) (b 2) (u 1) (u 3) (u 2) (y 1) (y 3) (y 2)
          hua'' hub'' hya'' hyb'' h13ne
        intro i j
        fin_cases i <;> fin_cases j <;> dsimp <;>
          first
          | rfl
          | exact h12 | exact h12.symm
          | exact h13 | exact h13.symm
          | exact h32 | exact h32.symm
          | (rw [hu0, hy0]; ring)
    · -- k = 1: u 1 = 0, y 1 = 0
      have hu1 : u 1 = 0 := hk
      have hy1 : y 1 = 0 := hyk
      have hua' : u 0 * a 0 + u 2 * a 2 + u 3 * a 3 = 0 := by
        have := hua; simp only [Fin.sum_univ_four] at this; rw [hu1] at this; linarith
      have hub' : u 0 * b 0 + u 2 * b 2 + u 3 * b 3 = 0 := by
        have := hub; simp only [Fin.sum_univ_four] at this; rw [hu1] at this; linarith
      have hya' : y 0 * a 0 + y 2 * a 2 + y 3 * a 3 = 0 := by
        have := hya; simp only [Fin.sum_univ_four] at this; rw [hy1] at this; linarith
      have hyb' : y 0 * b 0 + y 2 * b 2 + y 3 * b 3 = 0 := by
        have := hyb; simp only [Fin.sum_univ_four] at this; rw [hy1] at this; linarith
      have hminors : a 0 * b 2 - a 2 * b 0 ≠ 0 ∨ a 0 * b 3 - a 3 * b 0 ≠ 0 := by
        by_contra! h
        rcases h with ⟨h02, h03⟩
        have hid := four_point_primitive_boundary_kernel_is_atom_helper_x1 a b x hxa hxb
        rw [h02, h03] at hid
        have hid2 : x 1 * (a 0 * b 1 - a 1 * b 0) = 0 := by linarith
        have hx1 : x 1 ≠ 0 := (hx 1).ne'
        have : a 0 * b 1 - a 1 * b 0 = 0 := by
          cases mul_eq_zero.mp hid2 with
          | inl h => exact False.elim (hx1 h)
          | inr h => exact h
        exact hind this
      rcases hminors with h02ne | h03ne
      · have ⟨h02, h03, h23⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
          (a 0) (a 2) (a 3) (b 0) (b 2) (b 3) (u 0) (u 2) (u 3) (y 0) (y 2) (y 3)
          hua' hub' hya' hyb' h02ne
        intro i j
        fin_cases i <;> fin_cases j <;> dsimp <;>
          first
          | rfl
          | exact h02 | exact h02.symm
          | exact h03 | exact h03.symm
          | exact h23 | exact h23.symm
          | (rw [hu1, hy1]; ring)
      · have hua'' : u 0 * a 0 + u 3 * a 3 + u 2 * a 2 = 0 := by linarith
        have hub'' : u 0 * b 0 + u 3 * b 3 + u 2 * b 2 = 0 := by linarith
        have hya'' : y 0 * a 0 + y 3 * a 3 + y 2 * a 2 = 0 := by linarith
        have hyb'' : y 0 * b 0 + y 3 * b 3 + y 2 * b 2 = 0 := by linarith
        have ⟨h03, h02, h32⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
          (a 0) (a 3) (a 2) (b 0) (b 3) (b 2) (u 0) (u 3) (u 2) (y 0) (y 3) (y 2)
          hua'' hub'' hya'' hyb'' h03ne
        intro i j
        fin_cases i <;> fin_cases j <;> dsimp <;>
          first
          | rfl
          | exact h02 | exact h02.symm
          | exact h03 | exact h03.symm
          | exact h32 | exact h32.symm
          | (rw [hu1, hy1]; ring)
    · -- k = 2: u 2 = 0, y 2 = 0
      have hu2 : u 2 = 0 := hk
      have hy2 : y 2 = 0 := hyk
      have hua' : u 0 * a 0 + u 1 * a 1 + u 3 * a 3 = 0 := by
        have := hua; simp only [Fin.sum_univ_four] at this; rw [hu2] at this; linarith
      have hub' : u 0 * b 0 + u 1 * b 1 + u 3 * b 3 = 0 := by
        have := hub; simp only [Fin.sum_univ_four] at this; rw [hu2] at this; linarith
      have hya' : y 0 * a 0 + y 1 * a 1 + y 3 * a 3 = 0 := by
        have := hya; simp only [Fin.sum_univ_four] at this; rw [hy2] at this; linarith
      have hyb' : y 0 * b 0 + y 1 * b 1 + y 3 * b 3 = 0 := by
        have := hyb; simp only [Fin.sum_univ_four] at this; rw [hy2] at this; linarith
      have ⟨h01, h03, h13⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
        (a 0) (a 1) (a 3) (b 0) (b 1) (b 3) (u 0) (u 1) (u 3) (y 0) (y 1) (y 3)
        hua' hub' hya' hyb' hind
      intro i j
      fin_cases i <;> fin_cases j <;> dsimp <;>
        first
        | rfl
        | exact h01 | exact h01.symm
        | exact h03 | exact h03.symm
        | exact h13 | exact h13.symm
        | (rw [hu2, hy2]; ring)
    · -- k = 3: u 3 = 0, y 3 = 0
      have hu3 : u 3 = 0 := hk
      have hy3 : y 3 = 0 := hyk
      have hua' : u 0 * a 0 + u 1 * a 1 + u 2 * a 2 = 0 := by
        have := hua; simp only [Fin.sum_univ_four] at this; rw [hu3] at this; linarith
      have hub' : u 0 * b 0 + u 1 * b 1 + u 2 * b 2 = 0 := by
        have := hub; simp only [Fin.sum_univ_four] at this; rw [hu3] at this; linarith
      have hya' : y 0 * a 0 + y 1 * a 1 + y 2 * a 2 = 0 := by
        have := hya; simp only [Fin.sum_univ_four] at this; rw [hy3] at this; linarith
      have hyb' : y 0 * b 0 + y 1 * b 1 + y 2 * b 2 = 0 := by
        have := hyb; simp only [Fin.sum_univ_four] at this; rw [hy3] at this; linarith
      have ⟨h01, h02, h12⟩ := four_point_primitive_boundary_kernel_is_atom_helper_3
        (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) (u 0) (u 1) (u 2) (y 0) (y 1) (y 2)
        hua' hub' hya' hyb' hind
      intro i j
      fin_cases i <;> fin_cases j <;> dsimp <;>
        first
        | rfl
        | exact h01 | exact h01.symm
        | exact h02 | exact h02.symm
        | exact h12 | exact h12.symm
        | (rw [hu3, hy3]; ring)
  exact four_point_primitive_boundary_kernel_is_atom_helper_prop u y hu hun hy0 hyu hprop hprimitive
