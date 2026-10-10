import AFTD.Prelude

/-!
# standParamAsMatrix

Topic: quantum_field_theory   Node: 7770b6ccd540

Provenance: formalization of a published result. Source: Physlib, `standParamAsMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/StandardParameterization/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given four reals `θ₁₂ θ₁₃ θ₂₃ δ₁₃` the standard parameterization of the CKM matrix as a `3×3` complex matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
open ComplexConjugate in
/-- Given four reals `θ₁₂ θ₁₃ θ₂₃ δ₁₃` the standard parameterization of the CKM matrix as a `3×3` complex matrix. -/
noncomputable def standParamAsMatrix (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![Real.cos θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₃ * exp (-I * δ₁₃)],
    ![(-Real.sin θ₁₂ * Real.cos θ₂₃) - (Real.cos θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₁₂ * Real.cos θ₂₃ - Real.sin θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃),
      Real.sin θ₂₃ * Real.cos θ₁₃],
    ![Real.sin θ₁₂ * Real.sin θ₂₃ - Real.cos θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃),
      (-Real.cos θ₁₂ * Real.sin θ₂₃) - (Real.sin θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₂₃ * Real.cos θ₁₃]]
