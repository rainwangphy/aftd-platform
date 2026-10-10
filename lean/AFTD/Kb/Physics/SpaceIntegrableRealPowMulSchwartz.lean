import AFTD.Prelude

/-!
# Space.integrable_real_pow_mul_schwartz

Topic: classical_mechanics   Node: 5cc44f8a5f3c

Provenance: formalization of a published result. Source: Physlib, `Space.integrable_real_pow_mul_schwartz`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Norm/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.integrable_real_pow_mul_schwartz
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SchwartzMap NNReal in
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F] in
open MeasureTheory in
open InnerProductSpace in
open scoped Topology BigOperators FourierTransform in
open Distribution in
lemma Space.integrable_real_pow_mul_schwartz
    (ψ : 𝓢(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * ψ x) volume := by
  refine (ψ.integrable_pow_mul volume k).mono' (by fun_prop)
    (ae_of_all _ fun x => by simp [norm_mul, norm_pow])
