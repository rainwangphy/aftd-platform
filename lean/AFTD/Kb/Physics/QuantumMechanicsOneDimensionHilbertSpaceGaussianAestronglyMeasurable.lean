import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceGaussianIntegrable

/-!
# QuantumMechanics.OneDimension.HilbertSpace.gaussian_aestronglyMeasurable

Topic: quantum_mechanics   Node: 43eaf508126c

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.gaussian_aestronglyMeasurable`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.gaussian_aestronglyMeasurable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.gaussian_aestronglyMeasurable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) volume :=
  MeasureTheory.Integrable.aestronglyMeasurable (gaussian_integrable c hb)
