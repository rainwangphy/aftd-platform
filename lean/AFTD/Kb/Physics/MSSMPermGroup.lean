import AFTD.Prelude

/-!
# MSSM.PermGroup

Topic: quantum_field_theory   Node: 79853404f529

Provenance: formalization of a published result. Source: Physlib, `MSSM.PermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The group of family permutations is `S₃⁶`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
/-- The group of family permutations is `S₃⁶` -/
@[simp]
def MSSM.PermGroup := Fin 6 → Equiv.Perm (Fin 3)
