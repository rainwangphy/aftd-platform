import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstDecidableNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstFintype
import AFTD.Kb.Physics.CreateAnnihilateInstTotalNormalOrder

/-!
# CreateAnnihilate.instIsTransNormalOrder

Topic: quantum_field_theory   Node: 3bdba5eeea69

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.instIsTransNormalOrder`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Normal ordering is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Normal ordering is transitive. -/
instance CreateAnnihilate.instIsTransNormalOrder : IsTrans CreateAnnihilate normalOrder where
  trans := by decide
