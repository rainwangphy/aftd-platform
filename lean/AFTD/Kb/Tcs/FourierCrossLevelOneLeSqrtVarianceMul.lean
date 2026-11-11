import AFTD.Prelude
import AFTD.Kb.Tcs.FourierCrossLevel
import AFTD.Kb.Tcs.FourierVariance
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# fourier_cross_level_one_le_sqrt_variance_mul

Topic: combinatorics   Node: 04fbbcda1bd9

Provenance: helper lemma. step towards discrete_level_one_to_three_sharp_constant

Cauchy-Schwarz inequality for the first cross Fourier level: for any two functions f, g : {0,1}^n → ℝ, W_1[f, g] ≤ sqrt(Var(f) * Var(g)).
-/

/-- Cauchy-Schwarz inequality bounding cross level 1 Fourier weight by square root of variance product. -/
theorem fourier_cross_level_one_le_sqrt_variance_mul {n : ℕ}
    (f g : BooleanAnalysis.BooleanFunc n) :
    fourier_cross_level 1 f g ≤ Real.sqrt (fourier_variance f * fourier_variance g) := by
  set L := Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) with hL
  have hCS : (fourier_cross_level 1 f g)^2 ≤
      (∑ S ∈ L, BooleanAnalysis.fourierCoeff f S ^ 2) * (∑ S ∈ L, BooleanAnalysis.fourierCoeff g S ^ 2) := by
    rw [hL]
    rw [fourier_cross_level]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hkey : ∀ (h : BooleanAnalysis.BooleanFunc n),
      (∑ S ∈ L, BooleanAnalysis.fourierCoeff h S ^ 2) ≤ fourier_variance h := by
    intro h
    rw [fourier_variance]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS
      rw [hL, Finset.mem_powersetCard] at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.nonempty_iff_ne_empty]
      intro hh
      rw [hh] at hS
      simp at hS
    · intro S _ _
      exact sq_nonneg _
  have hA := hkey f
  have hB := hkey g
  have hBn : (0:ℝ) ≤ ∑ S ∈ L, BooleanAnalysis.fourierCoeff g S ^ 2 :=
    Finset.sum_nonneg (fun S _ => sq_nonneg _)
  have hvf : (0:ℝ) ≤ fourier_variance f := by
    rw [fourier_variance]; exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  have hAB : (∑ S ∈ L, BooleanAnalysis.fourierCoeff f S ^ 2) * (∑ S ∈ L, BooleanAnalysis.fourierCoeff g S ^ 2)
      ≤ fourier_variance f * fourier_variance g :=
    mul_le_mul hA hB hBn hvf
  calc fourier_cross_level 1 f g
      ≤ Real.sqrt ((fourier_cross_level 1 f g)^2) := Real.le_sqrt_of_sq_le (le_refl _)
    _ ≤ Real.sqrt ((∑ S ∈ L, BooleanAnalysis.fourierCoeff f S ^ 2) * (∑ S ∈ L, BooleanAnalysis.fourierCoeff g S ^ 2)) :=
        Real.sqrt_le_sqrt hCS
    _ ≤ Real.sqrt (fourier_variance f * fourier_variance g) := Real.sqrt_le_sqrt hAB
