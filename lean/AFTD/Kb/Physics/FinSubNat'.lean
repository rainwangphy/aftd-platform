import AFTD.Prelude

/-!
# Fin.subNat'

Topic: classical_mechanics   Node: cb1b4c00c322

Provenance: formalization of a published result. Source: Physlib, `Fin.subNat'`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`subNat' i h` subtracts `m` from `i`. This is an alternative form of `Fin.subNat`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- `subNat' i h` subtracts `m` from `i`. This is an alternative form of `Fin.subNat`. -/
@[inline] def Fin.subNat' (i : Fin (m + n)) (h : ¬ i < m) : Fin n :=
  subNat m (Fin.cast (m.add_comm n) i) (Nat.ge_of_not_lt h)
