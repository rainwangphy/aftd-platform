import AFTD.Prelude
import AFTD.Kb.Tcs.UnitComplexThreePhaseSurjective

/-!
# three_qubit_ghz_phase_compatibility

Topic: quantum   Node: 42d728a715b7

Provenance: helper lemma.

Four complex triple-correlation harmonics can all be made purely imaginary by three independent local transverse rotations exactly when the displayed gauge-invariant product is real, including vanishing harmonics.
-/

open Complex

lemma in935_align (z : ℂ) : ∃ a : ℂ, ‖a‖ = 1 ∧ (a*z).re = 0 := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · refine ⟨Complex.I * star z / (‖z‖ : ℂ), ?_, ?_⟩
    · simp [norm_div, norm_mul, norm_ne_zero_iff.mpr hz]
    · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
      have he : Complex.I * star z / (‖z‖ : ℂ) * z = Complex.I * (‖z‖ : ℂ) := by
        field_simp
        rw [Complex.star_def]
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [he]
      simp

lemma in935_product_unit (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖a*b*c‖ = 1 := by simp [norm_mul, ha, hb, hc]

lemma in935_invariant (a b c z0 z1 z2 z3 : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    z0 * star (z1*z2*z3) =
      (a*b*c*z0) * star ((a*z1)*(b*z2)*(c*z3)) := by
  have hsa : star a = a⁻¹ := (Complex.inv_eq_conj ha).symm
  have hsb : star b = b⁻¹ := (Complex.inv_eq_conj hb).symm
  have hsc : star c = c⁻¹ := (Complex.inv_eq_conj hc).symm
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  simp only [star_mul, hsa, hsb, hsc]
  field_simp
  <;> ring

lemma in935_pure_im_product (w x y z : ℂ)
    (hw : w.re = 0) (hx : x.re = 0) (hy : y.re = 0) (hz : z.re = 0) :
    (w * star (x*y*z)).im = 0 := by
  simp only [Complex.star_def, star_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    hw, hx, hy, hz]
  ring

lemma in935_lift (a b c z0 z1 z2 z3 : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (h0 : (a*b*c*z0).re = 0) (h1 : (a*z1).re = 0)
    (h2 : (b*z2).re = 0) (h3 : (c*z3).re = 0) :
    ∃ u v w : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (u*v*w*z0).re = 0 ∧ (u*v*star w*z1).re = 0 ∧
      (u*star v*w*z2).re = 0 ∧ (star u*v*w*z3).re = 0 := by
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := unit_complex_three_phase_surjective a b c ha hb hc
  have hsu : star u = u⁻¹ := (Complex.inv_eq_conj hu).symm
  have hsv : star v = v⁻¹ := (Complex.inv_eq_conj hv).symm
  have hsw : star w = w⁻¹ := (Complex.inv_eq_conj hw).symm
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have habc : a*b*c = u*v*w := by
    rw [← huv, ← huw, ← hvw, hsu, hsv, hsw]
    field_simp
    <;> ring
  refine ⟨u,v,w,hu,hv,hw, ?_, ?_, ?_, ?_⟩
  · rwa [habc] at h0
  · rwa [huv]
  · rwa [huw]
  · rwa [hvw]

lemma in935_zero_first (z0 z1 z2 z3 : ℂ) (hz : z1 = 0) :
    ∃ a b c : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧
      (a*b*c*z0).re = 0 ∧ (a*z1).re = 0 ∧ (b*z2).re = 0 ∧ (c*z3).re = 0 := by
  obtain ⟨d,hd,hdz⟩ := in935_align z0
  obtain ⟨b,hb,hbz⟩ := in935_align z2
  obtain ⟨c,hc,hcz⟩ := in935_align z3
  let a := d * star b * star c
  have ha : ‖a‖ = 1 := by simp [a, norm_mul, hd, hb, hc]
  have hsb : star b = b⁻¹ := (Complex.inv_eq_conj hb).symm
  have hsc : star c = c⁻¹ := (Complex.inv_eq_conj hc).symm
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have habc : a*b*c = d := by
    dsimp [a]
    change d * star b * star c * b * c = d
    rw [hsb, hsc]
    field_simp
  refine ⟨a,b,c,ha,hb,hc, ?_, ?_, hbz, hcz⟩
  · rwa [habc]
  · simp [hz]

lemma in935_nonzero_first_three (z0 z1 z2 z3 : ℂ)
    (h : (z0 * star (z1*z2*z3)).im = 0)
    (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (h3 : z3 ≠ 0) :
    ∃ a b c : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧
      (a*b*c*z0).re = 0 ∧ (a*z1).re = 0 ∧ (b*z2).re = 0 ∧ (c*z3).re = 0 := by
  let a : ℂ := I * star z1 / (‖z1‖ : ℂ)
  let b : ℂ := I * star z2 / (‖z2‖ : ℂ)
  let c : ℂ := I * star z3 / (‖z3‖ : ℂ)
  have ha : ‖a‖ = 1 := by simp [a, norm_ne_zero_iff.mpr h1]
  have hb : ‖b‖ = 1 := by simp [b, norm_ne_zero_iff.mpr h2]
  have hc : ‖c‖ = 1 := by simp [c, norm_ne_zero_iff.mpr h3]
  have align : ∀ (z : ℂ) (_ : z ≠ 0), (I * star z / (‖z‖ : ℂ) * z).re = 0 := by
    intro z hz
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    have he : I * star z / (‖z‖ : ℂ) * z = I * (‖z‖ : ℂ) := by
      field_simp
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [he]
    simp
  refine ⟨a,b,c,ha,hb,hc, ?_, align z1 h1, align z2 h2, align z3 h3⟩
  have he : a*b*c*z0 = -(I * (z0 * star (z1*z2*z3))) /
      ((‖z1‖ * ‖z2‖ * ‖z3‖ : ℝ) : ℂ) := by
    dsimp [a,b,c]
    simp only [star_mul, ofReal_mul]
    field_simp
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring
  rw [he]
  rw [Complex.div_ofReal_re]
  simp only [neg_re, Complex.I_mul_re, h, neg_zero, zero_div]

theorem three_qubit_ghz_phase_compatibility (z0 z1 z2 z3 : ℂ) :
    (∃ u v w : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (u*v*w*z0).re = 0 ∧
      (u*v*star w*z1).re = 0 ∧
      (u*star v*w*z2).re = 0 ∧
      (star u*v*w*z3).re = 0) ↔
    (z0 * star (z1*z2*z3)).im = 0 := by
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,h0,h1,h2,h3⟩
    let a : ℂ := u*v*star w
    let b : ℂ := u*star v*w
    let c : ℂ := star u*v*w
    have ha : ‖a‖ = 1 := by simp [a, hu, hv, hw]
    have hb : ‖b‖ = 1 := by simp [b, hu, hv, hw]
    have hc : ‖c‖ = 1 := by simp [c, hu, hv, hw]
    have hsu : star u = u⁻¹ := (Complex.inv_eq_conj hu).symm
    have hsv : star v = v⁻¹ := (Complex.inv_eq_conj hv).symm
    have hsw : star w = w⁻¹ := (Complex.inv_eq_conj hw).symm
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
    have habc : a*b*c = u*v*w := by
      dsimp [a,b,c]
      change (u*v*star w)*(u*star v*w)*(star u*v*w) = u*v*w
      rw [hsu, hsv, hsw]
      field_simp
    rw [in935_invariant a b c z0 z1 z2 z3 ha hb hc]
    apply in935_pure_im_product
    · simpa [habc] using h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    by_cases h1 : z1 = 0
    · obtain ⟨a,b,c,ha,hb,hc,h0,h1,h2,h3⟩ := in935_zero_first z0 z1 z2 z3 h1
      exact in935_lift a b c z0 z1 z2 z3 ha hb hc h0 h1 h2 h3
    by_cases h2 : z2 = 0
    · obtain ⟨a,b,c,ha,hb,hc,h0,h2,h1,h3⟩ := in935_zero_first z0 z2 z1 z3 h2
      apply in935_lift b a c z0 z1 z2 z3 hb ha hc
      · simpa [mul_comm, mul_left_comm, mul_assoc] using h0
      · exact h1
      · exact h2
      · exact h3
    by_cases h3 : z3 = 0
    · obtain ⟨a,b,c,ha,hb,hc,h0,h3,h2,h1⟩ := in935_zero_first z0 z3 z2 z1 h3
      apply in935_lift c b a z0 z1 z2 z3 hc hb ha
      · simpa [mul_comm, mul_left_comm, mul_assoc] using h0
      · exact h1
      · exact h2
      · exact h3
    obtain ⟨a,b,c,ha,hb,hc,h0,h1,h2,h3⟩ := in935_nonzero_first_three z0 z1 z2 z3 h h1 h2 h3
    exact in935_lift a b c z0 z1 z2 z3 ha hb hc h0 h1 h2 h3
