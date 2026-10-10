import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateNormalOrder
import AFTD.Kb.Physics.CreateAnnihilateInstFintype

/-!
# CreateAnnihilate.instDecidableNormalOrder

Topic: quantum_field_theory   Node: bff97901bc00

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.instDecidableNormalOrder`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normal ordering on `CreateAnnihilate` is decidable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The normal ordering on `CreateAnnihilate` is decidable. -/
instance CreateAnnihilate.instDecidableNormalOrder : (φ φ' : CreateAnnihilate) → Decidable (normalOrder φ φ')
  | create, create => isTrue True.intro
  | annihilate, annihilate => isTrue True.intro
  | create, annihilate => isTrue True.intro
  | annihilate, create => isFalse False.elim
