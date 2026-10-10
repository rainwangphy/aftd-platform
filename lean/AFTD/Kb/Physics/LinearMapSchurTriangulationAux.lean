import AFTD.Prelude

/-!
# LinearMap.SchurTriangulationAux

Topic: classical_mechanics   Node: d41128761490

Provenance: formalization of a published result. Source: Physlib, `LinearMap.SchurTriangulationAux`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`, `Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation`. See also `LinearMap.SchurTriangulationAux.of` and `Matrix.schurTriangulationAux`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
variable [RCLike 𝕜] in
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in
/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`, `Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation`. See also `LinearMap.SchurTriangulationAux.of` and `Matrix.schurTriangulationAux`. -/
structure LinearMap.SchurTriangulationAux (f : Module.End 𝕜 E) where
  /-- The dimension of the inner product space `E`. -/
  dim : ℕ
  hdim : Module.finrank 𝕜 E = dim
  /-- An orthonormal basis of `E` that induces an upper triangular form for `f`. -/
  basis : OrthonormalBasis (Fin dim) 𝕜 E
  upperTriangular : (toMatrix basis.toBasis basis.toBasis f).IsUpperTriangular
