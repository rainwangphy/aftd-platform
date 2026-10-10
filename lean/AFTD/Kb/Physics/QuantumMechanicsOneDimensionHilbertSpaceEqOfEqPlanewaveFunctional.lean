import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpacePlanewaveFunctional

/-!
# QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_planewaveFunctional

Topic: quantum_mechanics   Node: 1715640ff814

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_planewaveFunctional`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PlaneWaves.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two elements of the Schwartz submodule are equal if and only if they are equal on all applications of `planewaveFunctional`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap TemperedDistribution in
/-- Two elements of the Schwartz submodule are equal if and only if they are equal on all applications of `planewaveFunctional`. -/
lemma QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_planewaveFunctional {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ k, planewaveFunctional k ψ1 = planewaveFunctional k ψ2) :
    ψ1 = ψ2 :=
  (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective (SchwartzMap.ext h)
