import AFTD.Prelude
import AFTD.Kb.Physics.PureU1PermGroup

/-!
# PureU1.instGroupPermGroup

Topic: quantum_field_theory   Node: 0db305b426d3

Provenance: formalization of a published result. Source: Physlib, `PureU1.instGroupPermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `PermGroup n` inherits the instance of a group from `Equiv.Perm`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
/-- The type `PermGroup n` inherits the instance of a group from `Equiv.Perm`. -/
instance PureU1.instGroupPermGroup {n : ℕ} : Group (PermGroup n) := Equiv.Perm.permGroup
