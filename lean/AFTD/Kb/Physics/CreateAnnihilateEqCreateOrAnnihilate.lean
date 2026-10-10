import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateInstFintype

/-!
# CreateAnnihilate.eq_create_or_annihilate

Topic: quantum_field_theory   Node: ae381799362f

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.eq_create_or_annihilate`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CreateAnnihilate.eq_create_or_annihilate
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma CreateAnnihilate.eq_create_or_annihilate (φ : CreateAnnihilate) : φ = create ∨ φ = annihilate := by
  cases φ <;> simp
