import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsRectangularBarrier
import AFTD.Kb.Physics.QuantumMechanicsRectangularBarrierMPos
import AFTD.Kb.Physics.QuantumMechanicsRectangularBarrierMNonneg

/-!
# QuantumMechanics.RectangularBarrier.m_ne_zero

Topic: quantum_mechanics   Node: 4b21514e1617

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.RectangularBarrier.m_ne_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/RectangularBarrier/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.RectangularBarrier.m_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
open Set MeasureTheory in
variable (Q : RectangularBarrier) in
@[simp]
lemma QuantumMechanics.RectangularBarrier.m_ne_zero : Q.m ≠ 0 := Q.hm.ne'
