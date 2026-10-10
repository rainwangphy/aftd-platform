import AFTD.Prelude
import AFTD.Kb.Physics.Space

/-!
# Space.eq_of_val

Topic: classical_mechanics   Node: ade8bd2b844c

Provenance: formalization of a published result. Source: Physlib, `Space.eq_of_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.eq_of_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Space.eq_of_val {d} {p q : Space d} (h : p.val = q.val) :
    p = q := by
  cases p
  cases q
  congr
