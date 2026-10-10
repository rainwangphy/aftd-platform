import AFTD.Prelude

/-!
# SM.PermGroup

Topic: quantum_field_theory   Node: 4cdbe528f5a8

Provenance: formalization of a published result. Source: Physlib, `SM.PermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The group of `Sₙ` permutations for each species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def SM.PermGroup (n : ℕ) := ∀ (_ : Fin 5), Equiv.Perm (Fin n)
