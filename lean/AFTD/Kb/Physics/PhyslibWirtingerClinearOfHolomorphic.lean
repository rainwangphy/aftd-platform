import AFTD.Prelude

/-!
# Physlib.Wirtinger.clinear_of_holomorphic

Topic: classical_mechanics   Node: c9f671ce4c09

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.clinear_of_holomorphic`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The real derivative of a holomorphic `f : E → ℂ` is `ℂ`-linear along every direction — the hypothesis the foundation collapse `dWirtingerDir_eq_of_clinear` consumes. A holomorphic `f` has `fderiv ℝ f u = (fderiv ℂ f u).restrictScalars ℝ` (`DifferentiableAt.fderiv_restrictScalars`), so its real derivative agrees with the `ℂ`-linear complex derivative on every direction. Used at `E = ι → ℂ` for the coordinate collapse and at `E = ℂ` for the outer-`g` chain rule (§D).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
/-- The real derivative of a holomorphic `f : E → ℂ` is `ℂ`-linear along every direction — the hypothesis the foundation collapse `dWirtingerDir_eq_of_clinear` consumes. A holomorphic `f` has `fderiv ℝ f u = (fderiv ℂ f u).restrictScalars ℝ` (`DifferentiableAt.fderiv_restrictScalars`), so its real derivative agrees with the `ℂ`-linear complex derivative on every direction. Used at `E = ι → ℂ` for the coordinate collapse and at `E = ℂ` for the outer-`g` chain rule (§D). -/
lemma Physlib.Wirtinger.clinear_of_holomorphic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {u : E}
    (hf : DifferentiableAt ℂ f u) (d : E) :
    fderiv ℝ f u (Complex.I • d) = Complex.I • fderiv ℝ f u d := by
  rw [DifferentiableAt.fderiv_restrictScalars ℝ hf, ContinuousLinearMap.coe_restrictScalars',
    map_smul]
