import AFTD.Prelude

/-!
# Complex.ofReal_hasDerivAt

Topic: quantum_mechanics   Node: 8556c2902fde

Provenance: formalization of a published result. Source: Physlib, `Complex.ofReal_hasDerivAt`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Complex.ofReal_hasDerivAt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Complex.ofReal_hasDerivAt : HasDerivAt Complex.ofReal 1 x := by
  let f1 : ℂ → ℂ := id
  change HasDerivAt (f1 ∘ Complex.ofReal) 1 x
  apply HasDerivAt.comp_ofReal
  simp only [f1]
  exact hasDerivAt_id _
