import AFTD.Prelude

/-!
# lorentzAlgebra.instUniformSpaceMatrix

Topic: special_relativity   Node: d35ddaec58e1

Provenance: formalization of a published result. Source: Physlib, `lorentzAlgebra.instUniformSpaceMatrix`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzAlgebra/ExponentialMap.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

lorentzAlgebra.instUniformSpaceMatrix
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
attribute [local instance] Matrix.linftyOpNormedAlgebra in
attribute [local instance] Matrix.linftyOpNormedRing in
attribute [local instance] Matrix.instCompleteSpace in
open Complex in
attribute [local instance] Matrix.linftyOpNormedAlgebra in
noncomputable instance lorentzAlgebra.instUniformSpaceMatrix [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance
