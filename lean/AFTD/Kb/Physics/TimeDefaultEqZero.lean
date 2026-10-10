import AFTD.Prelude

/-!
# Time.default_eq_zero

Topic: classical_mechanics   Node: 75b8265f6591

Provenance: formalization of a published result. Source: Physlib, `Time.default_eq_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/InnerProductSpace.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.default_eq_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Time.default_eq_zero : default = 0 := rfl
