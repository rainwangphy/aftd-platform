import AFTD.Prelude
import AFTD.Kb.Physics.GroupTheorySO3
import AFTD.Kb.Physics.GroupTheorySO3Group
import AFTD.Kb.Physics.GroupTheoryInstTopologicalSpaceSO3

/-!
# GroupTheory.SO3.coe_inv

Topic: classical_mechanics   Node: 6d98d8e4d3f8

Provenance: formalization of a published result. Source: Physlib, `GroupTheory.SO3.coe_inv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SO3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

GroupTheory.SO3.coe_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
lemma GroupTheory.SO3.coe_inv (A : SO3) : (A⁻¹).1 = A.1⁻¹ :=
  (inv_eq_left_inv (mul_eq_one_comm.mpr A.2.2)).symm
