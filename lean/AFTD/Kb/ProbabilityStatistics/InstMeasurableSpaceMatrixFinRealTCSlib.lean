import AFTD.Prelude

/-!
# instMeasurableSpaceMatrixFinReal_tCSlib

Topic: concentration   Node: 9b8e0aba4421

Provenance: formalization of a published result. Source: TCSlib, `instMeasurableSpaceMatrixFinReal_tCSlib`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrices as `m → n → α` inherit a Pi measurable space structure.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- Matrices as `m → n → α` inherit a Pi measurable space structure. -/
noncomputable instance instMeasurableSpaceMatrixFinReal_tCSlib : MeasurableSpace (Matrix (Fin k) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin d → ℝ))
