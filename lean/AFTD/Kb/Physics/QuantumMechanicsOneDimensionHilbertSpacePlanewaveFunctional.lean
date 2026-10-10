import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule
import AFTD.Kb.Tcs.KnillLaflamme

/-!
# QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional

Topic: quantum_mechanics   Node: 16bd9be0069d

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PlaneWaves.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Plane waves as a member of the dual of the Schwartz submodule of the Hilbert space. For a given `k` this corresponds to the plane wave `exp (2π I k x)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap TemperedDistribution in
/-- Plane waves as a member of the dual of the Schwartz submodule of the Hilbert space. For a given `k` this corresponds to the plane wave `exp (2π I k x)`. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional (k : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (TemperedDistribution.delta k : SchwartzMap ℝ ℂ →L[ℂ] ℂ) ∘L (SchwartzMap.fourierTransformCLM ℂ)
