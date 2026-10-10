import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsInfiniteSquareWell
import AFTD.Kb.Physics.QuantumMechanicsInfiniteSquareWellMPos
import AFTD.Kb.Physics.QuantumMechanicsInfiniteSquareWellMNonneg

/-!
# QuantumMechanics.InfiniteSquareWell.m_ne_zero

Topic: quantum_mechanics   Node: fb3df2eb8dd8

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.InfiniteSquareWell.m_ne_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/InfiniteSquareWell/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.InfiniteSquareWell.m_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
open Set MeasureTheory in
variable {d : ℕ} (Q : InfiniteSquareWell d) in
@[simp]
lemma QuantumMechanics.InfiniteSquareWell.m_ne_zero : Q.m ≠ 0 := Q.hm.ne'
