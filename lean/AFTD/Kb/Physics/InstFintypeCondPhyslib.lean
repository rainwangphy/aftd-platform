import AFTD.Prelude

/-!
# instFintypeCond_physlib

Topic: classical_mechanics   Node: 45ec2771bcba

Provenance: formalization of a published result. Source: Physlib, `instFintypeCond_physlib`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type family parameterized by `Bool` is finite if each type variant is finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- The type family parameterized by `Bool` is finite if each type variant is finite. -/
instance instFintypeCond_physlib [M : Fintype m] [N : Fintype n] (b : Bool) : Fintype (cond b m n) := b.rec N M
