import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix

/-!
# CKMMatrix_ext

Topic: quantum_field_theory   Node: 164c7f982f7e

Provenance: formalization of a published result. Source: Physlib, `CKMMatrix_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two CKM matrices are equal if their underlying unitary matrices are equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- Two CKM matrices are equal if their underlying unitary matrices are equal. -/
lemma CKMMatrix_ext {U V : CKMMatrix} (h : U.val = V.val) : U = V := Subtype.ext h
