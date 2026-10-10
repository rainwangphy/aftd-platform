import AFTD.Prelude

/-!
# PureU1.LineInPlaneProp

Topic: quantum_field_theory   Node: d24d6165bfe9

Provenance: formalization of a published result. Source: Physlib, `PureU1.LineInPlaneProp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/LineInPlaneCond.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The proposition on three rationals to satisfy the `linInPlane` condition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {n : ℕ} in
/-- The proposition on three rationals to satisfy the `linInPlane` condition. -/
def PureU1.LineInPlaneProp : ℚ × ℚ × ℚ → Prop := fun s =>
  s.1 = s.2.1 ∨ s.1 = - s.2.1 ∨ 2 * s.2.2 + s.1 + s.2.1 = 0
