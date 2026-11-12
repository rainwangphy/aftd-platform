import AFTD.Prelude
import AFTD.Kb.Tcs.IsCoverable
import AFTD.Kb.Tcs.TriangularLattice
import AFTD.Kb.NumberTheory.EisensteinOmega

/-!
# triangular_lattice_coverable_critical_spacings

Topic: combinatorics   Node: 40344e248bde

Provenance: formalization of a published result. Source: arXiv:2611.13535 Theorem C -- Covering the Triangular Lattice with Non-Overlapping Unit Disks

The triangular lattice with spacing d is coverable by pairwise non-overlapping closed unit disks for d = 1 / Real.sqrt 13 and for d = 2 / Real.sqrt 21.
-/

open Complex

private lemma tlc_omega_sq : eisensteinOmega^2 + eisensteinOmega + 1 = 0 := by
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : eisensteinOmega.re = -1/2 := by simp [eisensteinOmega]
  have him : eisensteinOmega.im = Real.sqrt 3 / 2 := by simp [eisensteinOmega]
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, Complex.add_re, hre, him, Complex.zero_re, Complex.one_re]
    ring_nf
    nlinarith [h3]
  · simp only [pow_two, Complex.mul_im, Complex.add_im, hre, him, Complex.zero_im, Complex.one_im]
    ring_nf

private lemma tlc_omega_sq' : eisensteinOmega^2 = -eisensteinOmega - 1 := by
  linear_combination tlc_omega_sq

private lemma tlc_normSq_int (a b : ℤ) :
    Complex.normSq ((a:ℂ) + (b:ℂ)*eisensteinOmega) = ((a^2 - a*b + b^2 : ℤ) : ℝ) := by
  rw [Complex.normSq_apply]
  have hre : ((a:ℂ) + (b:ℂ)*eisensteinOmega).re = (a:ℝ) - (b:ℝ)/2 := by
    simp [eisensteinOmega, Complex.add_re, Complex.mul_re]; ring
  have him : ((a:ℂ) + (b:ℂ)*eisensteinOmega).im = (b:ℝ)*Real.sqrt 3 / 2 := by
    simp [eisensteinOmega, Complex.add_im, Complex.mul_im]; ring
  rw [hre, him]
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith [h3]

private lemma tlc_one_le_norm (a b : ℤ) (h : ((a:ℂ) + (b:ℂ)*eisensteinOmega) ≠ 0) :
    1 ≤ ‖(a:ℂ) + (b:ℂ)*eisensteinOmega‖ := by
  have hpos : 0 < Complex.normSq ((a:ℂ) + (b:ℂ)*eisensteinOmega) := by
    rwa [Complex.normSq_pos]
  rw [tlc_normSq_int] at hpos
  have hN : (1:ℤ) ≤ a^2 - a*b + b^2 := by
    have h0 : (0:ℤ) < a^2 - a*b + b^2 := by exact_mod_cast hpos
    nlinarith [h0]
  have hsq : (1:ℝ) ≤ ‖(a:ℂ) + (b:ℂ)*eisensteinOmega‖^2 := by
    rw [Complex.sq_norm, tlc_normSq_int]
    exact_mod_cast hN
  nlinarith [norm_nonneg ((a:ℂ) + (b:ℂ)*eisensteinOmega)]

private lemma tlc_coverable_of_data (d : ℝ) (hd : 0 < d) (β c₀ : ℂ) (n : ℝ)
    (hβ : Complex.normSq β = n) (hdn : d^2 * n = 4)
    (hcov : ∀ a b : ℤ, ∃ x y : ℤ,
      ‖2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*c₀ - 2*β*((x:ℂ) + (y:ℂ)*eisensteinOmega)‖^2 ≤ n) :
    is_coverable (triangular_lattice d) := by
  have hn : n = 4/d^2 := by
    field_simp at hdn ⊢
    linarith
  have hβnorm : ‖β‖ = 2/d := by
    have hsq : ‖β‖^2 = (2/d)^2 := by
      rw [Complex.sq_norm, hβ, hn]
      field_simp
      ring
    nlinarith [norm_nonneg β, (by positivity : (0:ℝ) ≤ 2/d)]
  have hd2 : (0:ℝ) < d/2 := by positivity
  refine ⟨{z : ℂ | ∃ x y : ℤ, z = (d:ℂ) * (c₀ + β*((x:ℂ) + (y:ℂ)*eisensteinOmega))}, ?_, ?_⟩
  · rintro c c' ⟨x, y, rfl⟩ ⟨x', y', rfl⟩ hne
    have hq : ((x:ℂ) + (y:ℂ)*eisensteinOmega) ≠ ((x':ℂ) + (y':ℂ)*eisensteinOmega) := by
      intro h; exact hne (by rw [h])
    have hdiff : ((x:ℂ) + (y:ℂ)*eisensteinOmega) - ((x':ℂ) + (y':ℂ)*eisensteinOmega)
        = ((x - x' : ℤ) : ℂ) + ((y - y' : ℤ) : ℂ)*eisensteinOmega := by push_cast; ring
    have hq' : ((x - x' : ℤ) : ℂ) + ((y - y' : ℤ) : ℂ)*eisensteinOmega ≠ 0 := by
      rw [← hdiff]; exact sub_ne_zero.mpr hq
    have hQ : 1 ≤ ‖((x - x' : ℤ) : ℂ) + ((y - y' : ℤ) : ℂ)*eisensteinOmega‖ :=
      tlc_one_le_norm _ _ hq'
    have hnorm : ‖(d:ℂ) * (c₀ + β*((x:ℂ) + (y:ℂ)*eisensteinOmega))
          - (d:ℂ) * (c₀ + β*((x':ℂ) + (y':ℂ)*eisensteinOmega))‖
        = d * (2/d) * ‖((x - x' : ℤ) : ℂ) + ((y - y' : ℤ) : ℂ)*eisensteinOmega‖ := by
      have he : (d:ℂ) * (c₀ + β*((x:ℂ) + (y:ℂ)*eisensteinOmega))
            - (d:ℂ) * (c₀ + β*((x':ℂ) + (y':ℂ)*eisensteinOmega))
          = (d:ℂ) * β * (((x - x' : ℤ) : ℂ) + ((y - y' : ℤ) : ℂ)*eisensteinOmega) := by
        rw [← hdiff]; ring
      rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, hβnorm]
    rw [hnorm, show d * (2/d) = 2 by field_simp]
    linarith
  · rintro z ⟨a, b, rfl⟩
    obtain ⟨x, y, hxy⟩ := hcov a b
    refine ⟨(d:ℂ) * (c₀ + β*((x:ℂ) + (y:ℂ)*eisensteinOmega)), ⟨x, y, rfl⟩, ?_⟩
    have hfac : (d:ℂ) * ((a:ℂ) + (b:ℂ)*eisensteinOmega)
          - (d:ℂ) * (c₀ + β*((x:ℂ) + (y:ℂ)*eisensteinOmega))
        = (d/2 : ℝ) * (2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*c₀
            - 2*β*((x:ℂ) + (y:ℂ)*eisensteinOmega)) := by
      push_cast; ring
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd2]
    have hW : ‖2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*c₀
        - 2*β*((x:ℂ) + (y:ℂ)*eisensteinOmega)‖ ≤ 2/d := by
      have hW2 : ‖2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*c₀
          - 2*β*((x:ℂ) + (y:ℂ)*eisensteinOmega)‖^2 ≤ (2/d)^2 := by
        rw [show (2/d)^2 = n from by rw [hn] at *; field_simp; ring]
        exact hxy
      nlinarith [norm_nonneg (2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*c₀
        - 2*β*((x:ℂ) + (y:ℂ)*eisensteinOmega)), (by positivity : (0:ℝ) ≤ 2/d)]
    have := mul_le_mul_of_nonneg_left hW hd2.le
    rwa [show d/2 * (2/d) = 1 by field_simp] at this

private def tlc13row (i j : Fin 2) : Fin 13 → ℤ × ℤ :=
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then
    ![(0, 0), (-2, -4), (2, 0), (-2, 2), (-4, -2), (0, 2), (-2, -2), (2, 2), (0, -2), (4, 2), (2, -2), (-2, 0), (2, 4)]
  else if (i : ℕ) = 0 then
    ![(-4, -1), (0, 3), (-2, -1), (2, 3), (0, -1), (4, 3), (2, -1), (-2, 1), (-4, -3), (0, 1), (-2, -3), (2, 1), (0, -3)]
  else if (j : ℕ) = 0 then
    ![(-3, -4), (1, 0), (-1, -4), (3, 0), (-1, 2), (-3, -2), (1, 2), (-1, -2), (3, 2), (1, -2), (-3, 0), (1, 4), (-1, 0)]
  else
    ![(-1, 3), (-3, -1), (1, 3), (-1, -1), (3, 3), (1, -1), (-3, 1), (3, -1), (-1, 1), (-3, -3), (1, 1), (-1, -3), (3, 1)]

private def tlc_tbl13 (i j : Fin 2) (r : Fin 13) : ℤ × ℤ := tlc13row i j r

private lemma tlc_tbl13_spec (i j : Fin 2) (r : Fin 13) :
    let p := tlc_tbl13 i j r
    (p.1 % 2 = ((i:ℕ):ℤ) ∧ p.2 % 2 = ((j:ℕ):ℤ) ∧
      (p.1 - 4*p.2) % 13 = ((r:ℕ):ℤ) ∧ p.1^2 - p.1*p.2 + p.2^2 ≤ 13) := by
  revert i j r
  decide

private lemma tlc_cover13 (a b : ℤ) :
    ∃ x y : ℤ, (a - 8*x + 2*y)^2 - (a - 8*x + 2*y)*(b - 2*x - 6*y) + (b - 2*x - 6*y)^2 ≤ 13 := by
  set m : ZMod 13 := (a : ZMod 13) - 4*(b : ZMod 13) with hm
  set i : Fin 2 := ⟨(a : ZMod 2).val, ZMod.val_lt (a : ZMod 2)⟩ with hi
  set j : Fin 2 := ⟨(b : ZMod 2).val, ZMod.val_lt (b : ZMod 2)⟩ with hj
  set r : Fin 13 := ⟨m.val, ZMod.val_lt m⟩ with hr
  obtain ⟨h1, h2, h3, h4⟩ := tlc_tbl13_spec i j r
  set u : ℤ := (tlc_tbl13 i j r).1 with hu
  set v : ℤ := (tlc_tbl13 i j r).2 with hv
  rw [hu] at h1 h3
  rw [hv] at h2 h3
  simp only [hu, hv] at h4
  have hi2 : ((i:ℕ):ℤ) = a % 2 := by
    simp only [hi]
    exact ZMod.val_intCast (n := 2) a
  have hj2 : ((j:ℕ):ℤ) = b % 2 := by
    simp only [hj]
    exact ZMod.val_intCast (n := 2) b
  have hm' : m = ((a - 4*b : ℤ) : ZMod 13) := by
    rw [hm]; push_cast; ring
  have hr2 : ((r:ℕ):ℤ) = (a - 4*b) % 13 := by
    simp only [hr]
    rw [hm']
    exact ZMod.val_intCast (n := 13) (a - 4*b)
  have k1 : u % 2 = a % 2 := by rw [h1, hi2]
  have k2 : v % 2 = b % 2 := by rw [h2, hj2]
  have k3 : (u - 4*v) % 13 = (a - 4*b) % 13 := by rw [h3, hr2]
  set K : ℤ := (((a - u) - 4*(b - v))/2)/13 with hK
  refine ⟨(b - v)/2 + 3*K, -K, ?_⟩
  have e1 : a - 8*((b - v)/2 + 3*K) + 2*(-K) = u := by omega
  have e2 : b - 2*((b - v)/2 + 3*K) - 6*(-K) = v := by omega
  rw [e1, e2]
  exact h4

private def tlc_tbl21 : Fin 21 → ℤ × ℤ :=
  ![(-5, -1), (-3, -5), (-3, -1), (-1, -5), (-1, -1), (-1, 3), (1, -1), (1, 3), (3, -1), (3, 3), (-5, -3), (5, 3),
    (-3, -3), (-3, 1), (-1, -3), (-1, 1), (1, -3), (1, 1), (1, 5), (3, 1), (3, 5)]

private lemma tlc_tbl21_spec (r : Fin 21) :
    let p := tlc_tbl21 r
    (p.1 % 2 = 1 ∧ p.2 % 2 = 1 ∧ (p.1 - 5*p.2) % 21 = ((r:ℕ):ℤ) ∧
      p.1^2 - p.1*p.2 + p.2^2 ≤ 21) := by
  revert r
  decide

private lemma tlc_cover21 (a b : ℤ) :
    ∃ x y : ℤ, (2*a - 3 - 10*x + 2*y)^2 - (2*a - 3 - 10*x + 2*y)*(2*b + 1 - 2*x - 8*y)
      + (2*b + 1 - 2*x - 8*y)^2 ≤ 21 := by
  set m : ZMod 21 := ((2*a - 3 : ℤ) : ZMod 21) - 5*((2*b + 1 : ℤ) : ZMod 21) with hm
  set r : Fin 21 := ⟨m.val, ZMod.val_lt m⟩ with hr
  obtain ⟨h1, h2, h3, h4⟩ := tlc_tbl21_spec r
  set u : ℤ := (tlc_tbl21 r).1 with hu
  set v : ℤ := (tlc_tbl21 r).2 with hv
  rw [hu] at h1 h3
  rw [hv] at h2 h3
  simp only [hu, hv] at h4
  have hm' : m = (((2*a - 3) - 5*(2*b + 1) : ℤ) : ZMod 21) := by
    rw [hm]; push_cast; ring
  have h3' : (u - 5*v) % 21 = ((2*a - 3) - 5*(2*b + 1)) % 21 := by
    rw [h3]
    simp only [hr]
    rw [hm']
    exact ZMod.val_intCast (n := 21) ((2*a - 3) - 5*(2*b + 1))
  set K : ℤ := ((((2*a - 3) - u) - 5*((2*b + 1) - v))/2)/21 with hK
  refine ⟨((2*b + 1) - v)/2 + 4*K, -K, ?_⟩
  have e1 : 2*a - 3 - 10*(((2*b + 1) - v)/2 + 4*K) + 2*(-K) = u := by omega
  have e2 : 2*b + 1 - 2*(((2*b + 1) - v)/2 + 4*K) - 8*(-K) = v := by omega
  rw [e1, e2]
  exact h4

private lemma tlc_coverable_one : is_coverable (triangular_lattice (1 / Real.sqrt 13)) := by
  have hd : (0:ℝ) < 1/Real.sqrt 13 := by positivity
  have hdn : (1/Real.sqrt 13)^2 * 52 = 4 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine tlc_coverable_of_data (1/Real.sqrt 13) hd (8 + 2*eisensteinOmega) 0 52 ?_ hdn ?_
  · have h := tlc_normSq_int 8 2
    norm_num at h
    exact h
  · intro a b
    obtain ⟨x, y, hxy⟩ := tlc_cover13 a b
    refine ⟨x, y, ?_⟩
    have e : 2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*(0:ℂ)
        - 2*(8 + 2*eisensteinOmega)*((x:ℂ) + (y:ℂ)*eisensteinOmega)
        = ((2*a - 16*x + 4*y : ℤ) : ℂ) + ((2*b - 4*x - 12*y : ℤ) : ℂ)*eisensteinOmega := by
      push_cast
      ring_nf
      rw [tlc_omega_sq']
      push_cast
      ring
    have hkey : ((2*a - 16*x + 4*y)^2 - (2*a - 16*x + 4*y)*(2*b - 4*x - 12*y)
        + (2*b - 4*x - 12*y)^2 : ℤ)
        = 4*((a - 8*x + 2*y)^2 - (a - 8*x + 2*y)*(b - 2*x - 6*y) + (b - 2*x - 6*y)^2) := by ring
    rw [e, Complex.sq_norm, tlc_normSq_int, hkey]
    have hZ : 4*((a - 8*x + 2*y)^2 - (a - 8*x + 2*y)*(b - 2*x - 6*y) + (b - 2*x - 6*y)^2) ≤ 52 := by
      linarith
    exact_mod_cast hZ

private lemma tlc_coverable_two : is_coverable (triangular_lattice (2 / Real.sqrt 21)) := by
  have hd : (0:ℝ) < 2/Real.sqrt 21 := by positivity
  have hdn : (2/Real.sqrt 21)^2 * 21 = 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine tlc_coverable_of_data (2/Real.sqrt 21) hd (5 + eisensteinOmega) ((3 - eisensteinOmega)/2) 21 ?_ hdn ?_
  · have h := tlc_normSq_int 5 1
    norm_num at h
    exact h
  · intro a b
    obtain ⟨x, y, hxy⟩ := tlc_cover21 a b
    refine ⟨x, y, ?_⟩
    have e : 2*((a:ℂ) + (b:ℂ)*eisensteinOmega) - 2*((3 - eisensteinOmega)/2)
        - 2*(5 + eisensteinOmega)*((x:ℂ) + (y:ℂ)*eisensteinOmega)
        = ((2*a - 3 - 10*x + 2*y : ℤ) : ℂ) + ((2*b + 1 - 2*x - 8*y : ℤ) : ℂ)*eisensteinOmega := by
      push_cast
      ring_nf
      rw [tlc_omega_sq']
      push_cast
      ring
    rw [e, Complex.sq_norm, tlc_normSq_int]
    exact_mod_cast hxy

/-- Coverability of the triangular lattice at spacings 1 / √13 and 2 / √21 by non-overlapping unit disks. -/
theorem triangular_lattice_coverable_critical_spacings : is_coverable (triangular_lattice (1 / Real.sqrt 13)) ∧ is_coverable (triangular_lattice (2 / Real.sqrt 21)) := ⟨tlc_coverable_one, tlc_coverable_two⟩
