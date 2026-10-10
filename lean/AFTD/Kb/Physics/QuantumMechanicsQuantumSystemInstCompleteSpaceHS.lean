import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS

/-!
# QuantumMechanics.QuantumSystem.instCompleteSpaceHS

Topic: quantum_mechanics   Node: 57da8f31ab7c

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.instCompleteSpaceHS`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.QuantumSystem.instCompleteSpaceHS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
noncomputable instance QuantumMechanics.QuantumSystem.instCompleteSpaceHS (Q : QuantumSystem) : CompleteSpace Q.HS := Q.instComplete
