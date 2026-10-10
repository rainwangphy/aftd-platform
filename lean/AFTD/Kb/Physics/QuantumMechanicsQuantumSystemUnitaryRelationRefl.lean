import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelation
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstCompleteSpaceHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstZero

/-!
# QuantumMechanics.QuantumSystem.unitaryRelation_refl

Topic: quantum_mechanics   Node: 493115484be1

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.unitaryRelation_refl`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `UnitaryRelation` is reflexive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- The relation `UnitaryRelation` is reflexive. -/
lemma QuantumMechanics.QuantumSystem.unitaryRelation_refl (Q : QuantumSystem) : UnitaryRelation Q Q :=
  ⟨LinearIsometryEquiv.refl _ _, by ext; simp [LinearIsometryEquiv.refl], by simp⟩
