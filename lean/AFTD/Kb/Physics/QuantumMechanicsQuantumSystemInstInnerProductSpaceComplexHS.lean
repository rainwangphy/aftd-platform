import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS

/-!
# QuantumMechanics.QuantumSystem.instInnerProductSpaceComplexHS

Topic: quantum_mechanics   Node: 2224bdf098a9

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.instInnerProductSpaceComplexHS`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.QuantumSystem.instInnerProductSpaceComplexHS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
noncomputable instance QuantumMechanics.QuantumSystem.instInnerProductSpaceComplexHS (Q : QuantumSystem) : InnerProductSpace ℂ Q.HS := Q.instInner
