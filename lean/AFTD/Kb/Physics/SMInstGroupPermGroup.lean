import AFTD.Prelude
import AFTD.Kb.Physics.SMPermGroup

/-!
# SM.instGroupPermGroup

Topic: quantum_field_theory   Node: a3a2a6bae371

Provenance: formalization of a published result. Source: Physlib, `SM.instGroupPermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `PermGroup n` inherits the instance of a group from it's target space `Equiv.Perm`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open Nat in
open Finset in
open BigOperators in
variable {n : ℕ} in
/-- The type `PermGroup n` inherits the instance of a group from it's target space `Equiv.Perm`. -/
@[simp]
instance SM.instGroupPermGroup : Group (PermGroup n) := Pi.group
