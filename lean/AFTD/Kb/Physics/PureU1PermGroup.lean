import AFTD.Prelude

/-!
# PureU1.PermGroup

Topic: quantum_field_theory   Node: 1f3168e2c9e7

Provenance: formalization of a published result. Source: Physlib, `PureU1.PermGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The permutation group of the n-fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
/-- The permutation group of the n-fermions. -/
@[simp]
def PureU1.PermGroup (n : ℕ) := Equiv.Perm (Fin n)
