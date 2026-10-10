import AFTD.Prelude

/-!
# SMRHN.PermGroup

Topic: quantum_field_theory   Node: 59660abc5c4d

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The group of `Sₙ` permutations for each species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def SMRHN.PermGroup (n : ℕ) := Fin 6 → Equiv.Perm (Fin n)
