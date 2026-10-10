import AFTD.Prelude

/-!
# Matrix.instUniformSpace_physlib

Topic: classical_mechanics   Node: 7fd347df7a15

Provenance: formalization of a published result. Source: Physlib, `Matrix.instUniformSpace_physlib`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.instUniformSpace_physlib
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators Topology in
variable {𝕂 m n : Type*} in
instance Matrix.instUniformSpace_physlib [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance
