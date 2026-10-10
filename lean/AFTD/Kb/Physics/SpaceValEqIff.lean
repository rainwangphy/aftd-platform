import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceEqOfVal

/-!
# Space.val_eq_iff

Topic: classical_mechanics   Node: fda2c18d7ccf

Provenance: formalization of a published result. Source: Physlib, `Space.val_eq_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.val_eq_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Space.val_eq_iff {d} {p q : Space d} :
    p.val = q.val ↔ p = q := by
  apply Iff.intro
  · exact eq_of_val
  · intro h
    rw [h]
