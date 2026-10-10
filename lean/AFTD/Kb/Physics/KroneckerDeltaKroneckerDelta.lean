import AFTD.Prelude

/-!
# KroneckerDelta.kroneckerDelta

Topic: classical_mechanics   Node: e3fc1a92d578

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.kroneckerDelta`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Kronecker delta function, `ite (i = j) 1 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α M : Type*} [DecidableEq α] in
/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def KroneckerDelta.kroneckerDelta (i j : α) : ℕ := if i = j then 1 else 0
