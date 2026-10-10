import AFTD.Prelude

/-!
# Constants.ℏ

Topic: quantum_mechanics   Node: 2867fc8b109b

Provenance: formalization of a published result. Source: Physlib, `Constants.ℏ`. Lean proof by Samyak Rai, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PlanckConstant.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The value of the reduced Planck's constant in units of J.s.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The value of the reduced Planck's constant in units of J.s. -/
def Constants.ℏ : Subtype fun x : ℝ => 0 < x := ⟨1.054571817e-34, by norm_num⟩
