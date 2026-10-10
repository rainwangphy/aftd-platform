import AFTD.Prelude

/-!
# Physlib.Wirtinger.fderiv_coordProj

Topic: classical_mechanics   Node: f69596cbde85

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_coordProj`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The real Fréchet derivative of the J-th coordinate projection `v ↦ v J`. Consumed by the Kronecker coordinate-value lemmas `dWirtingerCoord_coordProj` / `dWirtingerAntiCoord_coordProj`, which feed it the slot-I real and imaginary directions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
omit [Fintype ι] [DecidableEq ι] in
/-- The real Fréchet derivative of the J-th coordinate projection `v ↦ v J`. Consumed by the Kronecker coordinate-value lemmas `dWirtingerCoord_coordProj` / `dWirtingerAntiCoord_coordProj`, which feed it the slot-I real and imaginary directions. -/
lemma Physlib.Wirtinger.fderiv_coordProj (J : ι) (u d : (ι → ℂ)) :
    fderiv ℝ (fun v : (ι → ℂ) => v J) u d = d J := by
  rw [(hasFDerivAt_apply (𝕜 := ℝ) J u).fderiv, ContinuousLinearMap.proj_apply]
