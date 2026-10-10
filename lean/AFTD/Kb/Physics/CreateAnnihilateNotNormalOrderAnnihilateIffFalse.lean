import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstFintype
import AFTD.Kb.Physics.CreateAnnihilateInstDecidableNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstTotalNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstIsTransNormalOrder

/-!
# CreateAnnihilate.not_normalOrder_annihilate_iff_false

Topic: quantum_field_theory   Node: 5837a14b56be

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.not_normalOrder_annihilate_iff_false`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CreateAnnihilate.not_normalOrder_annihilate_iff_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma CreateAnnihilate.not_normalOrder_annihilate_iff_false (a : CreateAnnihilate) :
    (¬ normalOrder a annihilate) ↔ False := by
  cases a <;> simp [normalOrder]
