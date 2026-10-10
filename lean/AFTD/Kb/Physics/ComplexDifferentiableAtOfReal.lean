import AFTD.Prelude
import AFTD.Kb.Physics.ComplexOfRealHasDerivAt

/-!
# Complex.differentiableAt_ofReal

Topic: quantum_mechanics   Node: 82779b4f0155

Provenance: formalization of a published result. Source: Physlib, `Complex.differentiableAt_ofReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Complex.differentiableAt_ofReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[fun_prop]
lemma Complex.differentiableAt_ofReal : DifferentiableAt ℝ Complex.ofReal x := by
  exact HasFDerivAt.differentiableAt Complex.ofReal_hasDerivAt
