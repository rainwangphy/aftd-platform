import AFTD.Prelude

/-!
# ef1cost_arith

Topic: fair_division   Node: 6eeb95622851

The arithmetic heart of the upper bound.
-/

/-- The arithmetic heart of the upper bound. -/
lemma ef1cost_arith (a s t ρ x su ue ρu : ℝ)
    (h1 : a + s + t + ρ = 1) (h2 : x + su + ue + ρu = 1)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (hs0 : 0 ≤ s) (hρ0 : 0 ≤ ρ)
    (ht : 0 < t) (hue : t ≤ ue)
    (hF4 : su * t ≤ ue * s) (hF5 : ue * ρ ≤ ρu * t) (hF6 : a + s < ρ) :
    x + su ≤ ρu ∧ (ue + su) - (t + s) ≤ 3 - 2 * Real.sqrt 2 := by
  have ha0 : 0 ≤ a := le_trans hx0 hxa
  have hue0 : 0 ≤ ue := le_trans ht.le hue
  constructor
  · have k1 : ue * (a + s) ≤ ue * ρ := mul_le_mul_of_nonneg_left hF6.le hue0
    have k2 : t * a ≤ ue * a := mul_le_mul_of_nonneg_right hue ha0
    have k3 : t * x ≤ t * a := mul_le_mul_of_nonneg_left hxa ht.le
    have : t * (x + su) ≤ t * ρu := by nlinarith
    exact le_of_mul_le_mul_left this ht
  · set U := ue + su with hU
    set T := t + s with hT
    have hT0 : 0 ≤ T := by linarith
    have hi : U * t ≤ ue * T := by rw [hU, hT]; nlinarith
    have hUle : U ≤ 1 - ρu := by linarith
    have hii : U * t ≤ t - ue * ρ := by
      have := mul_le_mul_of_nonneg_right hUle ht.le
      nlinarith
    have hi' := mul_le_mul_of_nonneg_right hi hρ0
    have hii' := mul_le_mul_of_nonneg_right hii hT0
    have hiii : t * (U * (T + ρ)) ≤ t * T := by nlinarith
    have hiv : U * (T + ρ) ≤ T := le_of_mul_le_mul_left hiii ht
    have hTρ : T + ρ = 1 - a := by rw [hT]; linarith
    rw [hTρ] at hiv
    have hTa : T ≤ 1 - 2 * a := by rw [hT]; linarith
    have ha1 : 0 < 1 - a := by linarith
    have hv : (U - T) * (1 - a) ≤ a * (1 - 2 * a) := by
      have := mul_le_mul_of_nonneg_right hTa ha0
      nlinarith
    have h2' := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsq : a * (1 - 2 * a) ≤ (3 - 2 * Real.sqrt 2) * (1 - a) := by
      nlinarith [sq_nonneg (2 * a - (2 - Real.sqrt 2))]
    have : (U - T) * (1 - a) ≤ (3 - 2 * Real.sqrt 2) * (1 - a) := le_trans hv hsq
    exact le_of_mul_le_mul_right this ha1
