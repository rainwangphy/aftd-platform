import AFTD.Prelude

/-!
# Matrix.map_tsum

Topic: classical_mechanics   Node: ffe91fe4632a

Provenance: formalization of a published result. Source: Physlib, `Matrix.map_tsum`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.map_tsum
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators Topology in
variable {𝕂 m n : Type*} in
lemma Matrix.map_tsum {α β m n : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β]
    (f : α →+ β) (hf : Continuous f) {s : ℕ → Matrix m n α} (hs : Summable s) :
    (∑' k, s k).map f = ∑' k, (s k).map f := by
  let F : Matrix m n α →+ Matrix m n β := AddMonoidHom.mapMatrix f
  have hF : Continuous F := Continuous.matrix_map continuous_id hf
  exact (hs.hasSum.map F hF).tsum_eq.symm
