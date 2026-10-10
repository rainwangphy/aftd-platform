import AFTD.Prelude
import AFTD.Kb.Physics.GroupTheorySO3
import AFTD.Kb.Physics.GroupTheorySO3Group

/-!
# GroupTheory.instTopologicalSpaceSO3

Topic: classical_mechanics   Node: bf74bc1e7b58

Provenance: formalization of a published result. Source: Physlib, `GroupTheory.instTopologicalSpaceSO3`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SO3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SO3 has the subtype topology.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
/-- SO3 has the subtype topology. -/
instance GroupTheory.instTopologicalSpaceSO3 : TopologicalSpace SO3 := instTopologicalSpaceSubtype
