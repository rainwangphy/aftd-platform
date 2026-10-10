import AFTD.Prelude
import AFTD.Kb.Physics.ComplexOfRealHasDerivAt

/-!
# Complex.deriv_ofReal

Topic: quantum_mechanics   Node: 16470a929a93

Provenance: formalization of a published result. Source: Physlib, `Complex.deriv_ofReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Complex.deriv_ofReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Complex.deriv_ofReal : deriv Complex.ofReal x = 1 := by
  exact HasDerivAt.deriv Complex.ofReal_hasDerivAt
