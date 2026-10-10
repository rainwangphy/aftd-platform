import AFTD.Prelude
import AFTD.Kb.Physics.SMRHNPermGroup

/-!
# SMRHN.instGroupPermGroup

Topic: quantum_field_theory   Node: 538966adbada

Provenance: formalization of a published result. Source: Physlib, `SMRHN.instGroupPermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of a group on `PermGroup n` through the target space `Equiv.Perm (Fin n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN in
open Nat in
open Finset in
open BigOperators in
variable {n : ℕ} in
/-- The instance of a group on `PermGroup n` through the target space `Equiv.Perm (Fin n)`. -/
@[simp]
instance SMRHN.instGroupPermGroup : Group (PermGroup n) := Pi.group
