import AFTD.Prelude

/-!
# Physlib.Wirtinger.fderiv_comp_clm_apply

Topic: classical_mechanics   Node: 758d68e5ed84

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_comp_clm_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Chain rule for an inner continuous linear map `L`. Because the derivative of a linear map is the map itself, the real Fréchet derivative of `g ∘ L` at `u`, applied to `x`, equals the derivative of `g` at `L u` applied to `L x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedSpace ℂ V'] in
omit [NormedSpace ℂ V] [NormedSpace ℂ V'] in
/-- Chain rule for an inner continuous linear map `L`. Because the derivative of a linear map is the map itself, the real Fréchet derivative of `g ∘ L` at `u`, applied to `x`, equals the derivative of `g` at `L u` applied to `L x`. -/
lemma Physlib.Wirtinger.fderiv_comp_clm_apply {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hg : DifferentiableAt ℝ g (L u)) (x : V) :
    fderiv ℝ (fun p => g (L p)) u x = fderiv ℝ g (L u) (L x) :=
  DFunLike.congr_fun (hg.hasFDerivAt.comp u L.hasFDerivAt).fderiv x
