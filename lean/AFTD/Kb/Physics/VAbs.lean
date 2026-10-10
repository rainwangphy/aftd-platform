import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.CKMMatrixSetoid
import AFTD.Kb.Physics.VAbs'
import AFTD.Kb.Physics.VAbs'Equiv

/-!
# VAbs

Topic: quantum_field_theory   Node: 3f44f048d87d

Provenance: formalization of a published result. Source: Physlib, `VAbs`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The absolute value of the `(i,j)`th any representative of `⟦V⟧`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The absolute value of the `(i,j)`th any representative of `⟦V⟧`. -/
noncomputable def VAbs (i j : Fin 3) : Quotient CKMMatrixSetoid → ℝ :=
  Quotient.lift (fun V => VAbs' V i j) (VAbs'_equiv i j)
