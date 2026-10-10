import AFTD.Prelude

/-!
# Physlib.Distribution.norm_iteratedFDeriv_ofRealCLM

Topic: classical_mechanics   Node: f606edc9ede0

Provenance: formalization of a published result. Source: Physlib, `Physlib.Distribution.norm_iteratedFDeriv_ofRealCLM`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Distribution/PowMul.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Distribution.norm_iteratedFDeriv_ofRealCLM
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SchwartzMap NNReal in
variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] in
variable [NormedSpace ℝ E] in
open ContDiff in
open MeasureTheory in
lemma Physlib.Distribution.norm_iteratedFDeriv_ofRealCLM {x} (i : ℕ) :
    ‖iteratedFDeriv ℝ i (RCLike.ofRealCLM (K := 𝕜)) x‖ =
      if i = 0 then |x| else if i = 1 then 1 else 0 := by
  match i with
  | 0 => simp
  | 1 =>
    rw [norm_iteratedFDeriv_one, RCLike.ofRealCLM.fderiv]
    simp
  | (n + 2) =>
    have h : fderiv ℝ ⇑(RCLike.ofRealCLM (K := 𝕜)) = fun _ => RCLike.ofRealCLM := by
      ext1 y
      exact RCLike.ofRealCLM.fderiv
    rw [← norm_iteratedFDeriv_fderiv, h, iteratedFDeriv_const_of_ne n.succ_ne_zero]
    simp
