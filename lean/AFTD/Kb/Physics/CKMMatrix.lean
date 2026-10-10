import AFTD.Prelude

/-!
# CKMMatrix

Topic: quantum_field_theory   Node: 3ceed81c7ade

Provenance: formalization of a published result. Source: Physlib, `CKMMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of CKM matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The type of CKM matrices. -/
noncomputable def CKMMatrix : Type := unitaryGroup (Fin 3) ℂ
