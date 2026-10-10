import AFTD.Prelude
import AFTD.Kb.Physics.MatrixUpperTriangular
import AFTD.Kb.Physics.MatrixSchurTriangulationAux
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.schurTriangulation

Topic: classical_mechanics   Node: e52c7c1ada3b

Provenance: formalization of a published result. Source: Physlib, `Matrix.schurTriangulation`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an algebraically closed field is unitarily similar.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open scoped InnerProductSpace in
open Module in
variable [RCLike 𝕜] [IsAlgClosed 𝕜] [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n 𝕜) in
/-- The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an algebraically closed field is unitarily similar. -/
noncomputable def Matrix.schurTriangulation : UpperTriangular n 𝕜 :=
  A.schurTriangulationAux.2
