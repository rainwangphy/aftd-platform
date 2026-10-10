import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate
import AFTD.Kb.Physics.CreateAnnihilateInstFintype

/-!
# CreateAnnihilate.normalOrder

Topic: quantum_field_theory   Node: b8d422fafb09

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.normalOrder`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normal ordering on creation and annihilation operators. Under this relation, `normalOrder a b` is false only if `a` is annihilate and `b` is create.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The normal ordering on creation and annihilation operators. Under this relation, `normalOrder a b` is false only if `a` is annihilate and `b` is create. -/
def CreateAnnihilate.normalOrder : CreateAnnihilate → CreateAnnihilate → Prop
  | create, _ => True
  | annihilate, annihilate => True
  | annihilate, create => False
