import AFTD.Prelude
import AFTD.Kb.Tcs.ContinuousAntipodalCircleZero

/-!
# complex_continuous_odd_circle_extension_zero

Topic: quantum   Node: f78bbe6c10a5

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3 (the odd-map zero); this is a standard special case of the Borsuk–Ulam theorem.

A continuous complex-valued function on the complex plane that is odd on the unit circle has a zero somewhere in the plane.
-/

open Complex

theorem complex_continuous_odd_circle_extension_zero (g : ℂ → ℂ) (hg : Continuous g)
    (hodd : ∀ z : ℂ, Complex.normSq z = 1 → g (-z) = -g z) :
    ∃ z : ℂ, g z = 0 := by
  by_contra hn
  push_neg at hn
  have hsc : IsSimplyConnected (Set.univ : Set ℂ) := by
    letI : ContractibleSpace (Set.univ : Set ℂ) :=
      (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
    change SimplyConnectedSpace (Set.univ : Set ℂ)
    infer_instance
  have hzero : 0 ∉ g '' (Set.univ : Set ℂ) := by
    simp only [Set.image_univ, Set.mem_range, not_exists]
    intro z hz
    exact hn z hz
  obtain ⟨r,hrcont,hrpow⟩ := Complex.exists_continuousOn_pow_eq hsc isOpen_univ hg.continuousOn hzero (n := 2) (by norm_num)
  have hr : Continuous r := continuousOn_univ.mp hrcont
  have hrn (z : ℂ) : r z ≠ 0 := by
    intro h
    apply hn z
    rw [← hrpow z, h]
    norm_num
  let q : ℂ → ℂ := fun z => r (-z) / r z
  have hqcont : Continuous q := by
    dsimp [q]
    exact (hr.comp continuous_neg).div hr hrn
  have hq2 (z : ℂ) (hz : Complex.normSq z = 1) : (q z)^2 = -1 := by
    dsimp [q]
    rw [div_pow, hrpow (-z), hrpow z, hodd z hz]
    simp [hn z]
  have hqmul : q 1 * q (-1) = 1 := by
    dsimp [q]
    simp only [neg_neg]
    field_simp [hrn 1, hrn (-1)]
  have hs : (q 1)^2 = -1 := hq2 1 (by norm_num)
  have hqneg : q (-1) = -q 1 := by
    calc
      q (-1) = q (-1) * 1 := by ring
      _ = q (-1) * (-(q 1)^2) := by rw [hs]; ring
      _ = -(q 1) * (q 1 * q (-1)) := by ring
      _ = -q 1 := by rw [hqmul]; ring
  let f : ℝ × ℝ → ℝ := fun p => (q ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).im
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hflip : f (-1,0) = -f (1,0) := by
    simpa [f] using congrArg Complex.im hqneg
  obtain ⟨x,y,hxy,hzero⟩ := continuous_antipodal_circle_zero f hf hflip
  let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hz : Complex.normSq z = 1 := by
    simp only [z, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [hxy]
  have hsq := hq2 z hz
  have him : (q z).im = 0 := by simpa [f, z] using hzero
  have hre := congrArg Complex.re hsq
  simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.one_re] at hre
  rw [him] at hre
  nlinarith [sq_nonneg (q z).re]
