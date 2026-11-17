import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0LtOne
import AFTD.Kb.Tcs.MagicSquareSecantSlopeMonotone
import AFTD.Kb.Tcs.MagicSquareGuessFnGeLinear
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0
import AFTD.Kb.Tcs.MagicSquareGuessFn

/-!
# magic_square_predictability_slope_of_lower_bound

Topic: quantum   Node: 67f6a12036a4

Provenance: helper lemma. arXiv:2610.12001, Section 6 and Corollary 6.2; analysis of the right-hand secant limit.

Any uniform lower bound a on the predictability-loss secant slopes, together with the established upper bound, yields a finite right-hand slope between a and the upper bound.
-/

theorem in937_monotone_bounded_right_limit (f : ℝ → ℝ) (a b R : ℝ)
    (hR : 0 < R) (hm : MonotoneOn f (Set.Ioo 0 R))
    (ha : ∀ x ∈ Set.Ioo 0 R, a ≤ f x)
    (hb : ∀ x ∈ Set.Ioo 0 R, f x ≤ b) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  have hn : (Set.Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, by constructor <;> linarith⟩
  have hsn : (f '' Set.Ioo 0 R).Nonempty := hn.image f
  have hlow : BddBelow (f '' Set.Ioo 0 R) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ha x hx
  refine ⟨sInf (f '' Set.Ioo 0 R), ?_, ?_, ?_⟩
  · exact le_csInf hsn (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)
  · obtain ⟨x, hx⟩ := hn
    exact (csInf_le hlow ⟨x, hx, rfl⟩).trans (hb x hx)
  · exact hm.tendsto_nhdsWithin_Ioo_right hn hlow

theorem magic_square_predictability_slope_of_lower_bound (a : ℝ)
    (hlinear : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 - magic_square_threshold_beta0 →
      a * δ ≤ 1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ)) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ 3 / (4 * (1 - magic_square_threshold_beta0)) ∧
      Filter.Tendsto (fun δ : ℝ => (1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ)) / δ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  let β := magic_square_threshold_beta0
  let R := 1 - β
  let f := fun δ : ℝ => (1 - magic_square_guess_fn (β + δ)) / δ
  have hR : 0 < R := by dsimp [R, β]; linarith [magic_square_threshold_beta0_lt_one]
  apply in937_monotone_bounded_right_limit f (a) (3 / (4 * R)) R hR
  · intro x hx y hy hxy
    exact magic_square_secant_slope_monotone x y hx.1 hxy hy.2.le
  · intro x hx
    have hxR : x < 1 - magic_square_threshold_beta0 := by simpa [R, β] using hx.2
    have h := hlinear x hx.1.le hxR.le
    dsimp [f, β]
    apply (le_div_iff₀ hx.1).2
    simpa [mul_comm] using h
  · intro x hx
    have hxR : x < 1 - magic_square_threshold_beta0 := by simpa [R, β] using hx.2
    have h := magic_square_guess_fn_ge_linear x hx.1.le hxR.le
    dsimp [f]
    apply (div_le_iff₀ hx.1).2
    have heq : 3 / (4 * R) * x = 3 * x / (4 * R) := by ring
    rw [heq]
    simpa [R, β] using h
