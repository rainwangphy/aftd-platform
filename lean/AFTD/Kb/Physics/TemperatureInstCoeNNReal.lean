import AFTD.Prelude
import AFTD.Kb.Physics.Temperature

/-!
# Temperature.instCoeNNReal

Topic: statistical_mechanics   Node: bd4b57b7b528

Provenance: formalization of a published result. Source: Physlib, `Temperature.instCoeNNReal`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coercion to `ℝ≥0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Coercion to `ℝ≥0`. -/
instance Temperature.instCoeNNReal : Coe Temperature ℝ≥0 := ⟨fun T => T.val⟩
