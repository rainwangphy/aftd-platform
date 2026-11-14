import AFTD.Prelude

/-!
# ghz_exchange_harmonic_zero

Topic: quantum   Node: 27a99f6c8865

Provenance: helper lemma.

Four continuous complex harmonics whose endpoints transform by the displayed exchange-and-conjugation rule have a point at which their GHZ phase invariant vanishes.
-/

theorem ghz_exchange_harmonic_zero
    (z0 z1 z2 z3 : ℝ → ℂ)
    (h0 : Continuous z0) (h1 : Continuous z1)
    (h2 : Continuous z2) (h3 : Continuous z3)
    (e0 : z0 1 = z3 0) (e1 : z1 1 = star (z2 0))
    (e2 : z2 1 = z0 0) (e3 : z3 1 = star (z1 0)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (z0 t * star (z1 t * z2 t * z3 t)).im = 0 := by
  let f : ℝ → ℝ := fun t => (z0 t * star (z1 t * z2 t * z3 t)).im
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hflip : f 1 = -f 0 := by
    dsimp [f]
    rw [e0, e1, e2, e3]
    have heq : z3 0 * star (star (z2 0) * z0 0 * star (z1 0)) =
        star (z0 0 * star (z1 0 * z2 0 * z3 0)) := by
      simp only [star_mul, star_star]
      ring
    change (z3 0 * star (star (z2 0) * z0 0 * star (z1 0))).im =
      -(z0 0 * star (z1 0 * z2 0 * z3 0)).im
    rw [heq]
    simp
    <;> ring
  have hz : (0 : ℝ) ∈ f '' Set.Icc 0 1 := by
    rcases le_total (f 0) 0 with h | h
    · apply intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn
      exact ⟨h, by rw [hflip]; linarith⟩
    · apply intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn
      exact ⟨by rw [hflip]; linarith, h⟩
  obtain ⟨t, ht, hz⟩ := hz
  exact ⟨t, ht, hz⟩
