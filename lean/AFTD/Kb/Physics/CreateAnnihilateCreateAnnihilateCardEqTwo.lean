import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateInstFintype
import AFTD.Kb.Physics.CreateAnnihilateNotNormalOrderAnnihilateIffFalse
import AFTD.Kb.Physics.CreateAnnihilateInstDecidableNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstIsTransNormalOrder

/-!
# CreateAnnihilate.CreateAnnihilate_card_eq_two

Topic: quantum_field_theory   Node: 9b92e3a86f4c

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.CreateAnnihilate_card_eq_two`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CreateAnnihilate.CreateAnnihilate_card_eq_two
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma CreateAnnihilate.CreateAnnihilate_card_eq_two : Fintype.card CreateAnnihilate = 2 := rfl
