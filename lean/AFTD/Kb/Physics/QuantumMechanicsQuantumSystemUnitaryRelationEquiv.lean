import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystem
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelation
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelationRefl
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelationSymm
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemUnitaryRelationTrans
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstNormedAddCommGroupHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstInnerProductSpaceComplexHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstCompleteSpaceHS
import AFTD.Kb.Physics.QuantumMechanicsQuantumSystemInstZero

/-!
# QuantumMechanics.QuantumSystem.unitaryRelation_equiv

Topic: quantum_mechanics   Node: 05e1b9ce89d3

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem.unitaryRelation_equiv`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `UnitaryRelation` is an equivalence relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- The relation `UnitaryRelation` is an equivalence relation. -/
lemma QuantumMechanics.QuantumSystem.unitaryRelation_equiv : Equivalence UnitaryRelation where
  refl := unitaryRelation_refl
  symm := unitaryRelation_symm
  trans := unitaryRelation_trans
