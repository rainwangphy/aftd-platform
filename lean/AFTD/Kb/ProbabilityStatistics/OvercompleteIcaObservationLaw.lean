import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.GramCharlierPdf

/-!
# overcomplete_ica_observation_law

Topic: minimax   Node: ddf6e715f922

Provenance: formalization of a published result. Source: arXiv:2611.11852: Section 2

For a natural number q, real shape parameter a, and rotation angle θ : ℝ, the observation law overcomplete_ica_observation_law q a θ is the pushforward measure on Fin 2 → ℝ under the linear map mix(s) = ∑ j : Fin q, s j • col(j) of the q-fold product measure of the measure on ℝ with density ENNReal.ofReal (gram_charlier_pdf a s) with respect to Lebesgue measure volume, where the columns col(j) : Fin 2 → ℝ are scaled by Real.sqrt (2 / q) with components Real.cos (θ + j * π / q) and Real.sin (θ + j * π / q).
-/

/-- The observation law on Fin 2 → ℝ in the equally spaced overcomplete ICA model with rotation angle theta and Gram-Charlier sources. -/
noncomputable def overcomplete_ica_observation_law (q : ℕ) (a : ℝ) (θ : ℝ) : MeasureTheory.Measure (Fin 2 → ℝ) :=
  let μ_a : MeasureTheory.Measure ℝ := MeasureTheory.Measure.withDensity MeasureTheory.volume (fun s => ENNReal.ofReal (gram_charlier_pdf a s))
  let col : Fin q → Fin 2 → ℝ := fun j i =>
    Real.sqrt (2 / (q : ℝ)) *
      if i = 0 then Real.cos (θ + (j : ℝ) * Real.pi / q)
      else Real.sin (θ + (j : ℝ) * Real.pi / q)
  let mix : (Fin q → ℝ) → Fin 2 → ℝ := fun s => ∑ j : Fin q, s j • col j
  MeasureTheory.Measure.map mix (MeasureTheory.Measure.pi (fun (_ : Fin q) => μ_a))
