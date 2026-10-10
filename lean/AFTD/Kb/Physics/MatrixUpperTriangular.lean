import AFTD.Prelude

/-!
# Matrix.UpperTriangular

Topic: classical_mechanics   Node: b0612fb2c877

Provenance: formalization of a published result. Source: Physlib, `Matrix.UpperTriangular`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subtype of upper triangular matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- The subtype of upper triangular matrices. -/
abbrev Matrix.UpperTriangular (n R) [LT n] [CommRing R] := { A : Matrix n n R // A.IsUpperTriangular }
