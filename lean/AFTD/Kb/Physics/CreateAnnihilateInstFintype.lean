import AFTD.Prelude
import AFTD.Kb.Physics.CreateAnnihilate

/-!
# CreateAnnihilate.instFintype

Topic: quantum_field_theory   Node: ea13ccdfb806

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate.instFintype`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `CreateAnnihilate` is finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `CreateAnnihilate` is finite. -/
instance CreateAnnihilate.instFintype : Fintype CreateAnnihilate where
  elems := {create, annihilate}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self create {annihilate}
    · exact Finset.insert_eq_self.mp rfl
