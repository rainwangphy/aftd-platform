import AFTD.Prelude
import AFTD.Kb.Physics.Divergence
import AFTD.Kb.Physics.DivergenceZero

/-!
# divergence_eq_sum_fderiv

Topic: classical_mechanics   Node: 8b71143ca506

Provenance: formalization of a published result. Source: Physlib, `divergence_eq_sum_fderiv`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

divergence_eq_sum_fderiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
lemma divergence_eq_sum_fderiv {s : Finset E} (b : Basis s 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i : s, b.repr (fderiv 𝕜 f x (b i)) i := by
  funext x
  unfold divergence
  rw[LinearMap.trace_eq_matrix_trace_of_finset (s:=s) _ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rfl
