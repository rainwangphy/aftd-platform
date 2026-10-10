import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftRelation
import AFTD.Kb.Physics.PhaseShiftRelationRefl
import AFTD.Kb.Physics.PhaseShiftRelationSymm
import AFTD.Kb.Physics.PhaseShiftRelationTrans
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShiftRelation_equiv

Topic: quantum_field_theory   Node: c3f88960150b

Provenance: formalization of a published result. Source: Physlib, `phaseShiftRelation_equiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PhaseShiftRelation` is an equivalence relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PhaseShiftRelation` is an equivalence relation. -/
lemma phaseShiftRelation_equiv : Equivalence PhaseShiftRelation where
  refl := phaseShiftRelation_refl
  symm := phaseShiftRelation_symm
  trans := phaseShiftRelation_trans
