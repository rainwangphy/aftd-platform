import AFTD.Prelude
import AFTD.Kb.Physics.MatrixUpperTriangular
import AFTD.Kb.Physics.LinearMapSchurTriangulationAuxOf
import AFTD.Kb.Physics.LinearMapSchurTriangulationAux
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Matrix.schurTriangulationAux

Topic: classical_mechanics   Node: ca401ba0b7b1

Provenance: formalization of a published result. Source: Physlib, `Matrix.schurTriangulationAux`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

This is `LinearMap.SchurTriangulationAux` adapted for matrices in the Euclidean space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open scoped InnerProductSpace in
open Module in
variable [RCLike 𝕜] [IsAlgClosed 𝕜] [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n 𝕜) in
/-- This is `LinearMap.SchurTriangulationAux` adapted for matrices in the Euclidean space. -/
noncomputable def Matrix.schurTriangulationAux :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 :=
  let f := toEuclideanLin A
  let ⟨d, hd, b, hut⟩ := LinearMap.SchurTriangulationAux.of f
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let b' := b.reindex e
  let B := LinearMap.toMatrixOrthonormal b' f
  suffices B.IsUpperTriangular from ⟨b', B, this⟩
  fun i j (hji : j < i) =>
    calc LinearMap.toMatrixOrthonormal b' f i j
      _ = LinearMap.toMatrixOrthonormal b f (e.symm i) (e.symm j) := by
        rw [f.toMatrixOrthonormal_reindex]
        rfl
      _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)
