import AFTD.Prelude
import AFTD.Kb.Physics.MatrixUpperTriangular
import AFTD.Kb.Physics.MatrixSchurTriangulationAux
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.schurTriangulationBasis

Topic: classical_mechanics   Node: 4a6d2d7fa0c8

Provenance: formalization of a published result. Source: Physlib, `Matrix.schurTriangulationBasis`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The change of basis that induces the upper triangular form `A.schurTriangulation` of a matrix `A` over an algebraically closed field.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open scoped InnerProductSpace in
open Module in
variable [RCLike 𝕜] [IsAlgClosed 𝕜] [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n 𝕜) in
/-- The change of basis that induces the upper triangular form `A.schurTriangulation` of a matrix `A` over an algebraically closed field. -/
noncomputable def Matrix.schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  A.schurTriangulationAux.1
