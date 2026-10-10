import AFTD.Prelude
import AFTD.Kb.Physics.MatrixInstUniformSpacePhyslib
import AFTD.Kb.Physics.MatrixMapTsum

/-!
# NormedSpace.exp_map_algebraMap

Topic: classical_mechanics   Node: 7f7d8eca01f8

Provenance: formalization of a published result. Source: Physlib, `NormedSpace.exp_map_algebraMap`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

NormedSpace.exp_map_algebraMap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma NormedSpace.exp_map_algebraMap {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (exp A).map (algebraMap ℝ ℂ) = exp (A.map (algebraMap ℝ ℂ)) := by
  let : SeminormedRing (Matrix n n ℝ) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  let : CompleteSpace (Matrix n n ℝ) := inferInstance
  let : SeminormedRing (Matrix n n ℂ) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : CompleteSpace (Matrix n n ℂ) := inferInstance
  simp only [exp_eq_tsum ℝ]
  have hs : Summable (fun k => (k.factorial : ℝ)⁻¹ • A ^ k) := by
    exact NormedSpace.expSeries_summable' A
  erw [Matrix.map_tsum (algebraMap ℝ ℂ).toAddMonoidHom RCLike.continuous_ofReal hs]
  apply tsum_congr
  intro k
  erw [Matrix.map_smul, Matrix.map_pow A (algebraMap ℝ ℂ) k]
  simp
