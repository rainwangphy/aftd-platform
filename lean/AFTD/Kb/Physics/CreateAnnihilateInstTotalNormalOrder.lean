import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstDecidableNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstFintype

/-!
# CreateAnnihilate.instTotalNormalOrder

Topic: quantum_field_theory   Node: 3734f03bef34

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.instTotalNormalOrder`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Normal ordering is total.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Normal ordering is total. -/
instance CreateAnnihilate.instTotalNormalOrder : Std.Total normalOrder where
  total := by decide
