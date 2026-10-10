import AFTD.Prelude
import AFTD.Kb.Physics.MSSMPermGroup

/-!
# MSSM.instGroupPermGroup

Topic: quantum_field_theory   Node: 1a46afc902f9

Provenance: formalization of a published result. Source: Physlib, `MSSM.instGroupPermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `PermGroup` has a group instances derived from the group instance of it's target.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
/-- The type `PermGroup` has a group instances derived from the group instance of it's target. -/
@[simp]
instance MSSM.instGroupPermGroup : Group PermGroup := Pi.group
