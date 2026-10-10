import AFTD.Prelude

/-!
# QuantumMechanics.OneDimension.HilbertSpace.gaussian_integrable

Topic: quantum_mechanics   Node: 84eb900defa5

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.gaussian_integrable`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.gaussian_integrable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.gaussian_integrable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => (Real.exp (- b * (x - c)^ 2) : ℂ)) :=
  MeasureTheory.Integrable.ofReal (Integrable.comp_sub_right
    (f := (fun x => Real.exp (- b * x ^ 2))) (integrable_exp_neg_mul_sq hb) ..)
