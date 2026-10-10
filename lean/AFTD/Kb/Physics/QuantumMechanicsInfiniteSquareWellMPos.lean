import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsInfiniteSquareWell

/-!
# QuantumMechanics.InfiniteSquareWell.m_pos

Topic: quantum_mechanics   Node: 54268a65974d

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.InfiniteSquareWell.m_pos`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/InfiniteSquareWell/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.InfiniteSquareWell.m_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
open Set MeasureTheory in
variable {d : ℕ} (Q : InfiniteSquareWell d) in
@[simp]
lemma QuantumMechanics.InfiniteSquareWell.m_pos : 0 < Q.m := Q.hm
