import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateInstFintype
import AFTD.Kb.Physics.CreateAnnihilateNotNormalOrderAnnihilateIffFalse
import AFTD.Kb.Physics.CreateAnnihilateInstDecidableNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstIsTransNormalOrder

/-!
# CreateAnnihilate.sum_eq

Topic: quantum_field_theory   Node: 3a517562b955

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.sum_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CreateAnnihilate.sum_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma CreateAnnihilate.sum_eq {M : Type} [AddCommMonoid M] (f : CreateAnnihilate → M) :
    ∑ i, f i = f create + f annihilate := by
  change ∑ i ∈ {create, annihilate}, f i = f create + f annihilate
  simp
