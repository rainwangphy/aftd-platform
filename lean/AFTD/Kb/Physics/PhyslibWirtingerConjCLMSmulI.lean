import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerConjCLM
import AFTD.Kb.Physics.PhyslibWirtingerConjCLMApply

/-!
# Physlib.Wirtinger.conjCLM_smul_I

Topic: classical_mechanics   Node: 0369f2c1c2a6

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.conjCLM_smul_I`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`conjCLM` is conjugate-ℂ-linear: `conj (i·d) = -(i · conj d)`. The `hL` hypothesis the foundation `dWirtingerDir_comp_conjLinear` / `dWirtingerAntiDir_comp_conjLinear` consume.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
omit [Fintype ι] [DecidableEq ι] in
/-- `conjCLM` is conjugate-ℂ-linear: `conj (i·d) = -(i · conj d)`. The `hL` hypothesis the foundation `dWirtingerDir_comp_conjLinear` / `dWirtingerAntiDir_comp_conjLinear` consume. -/
lemma Physlib.Wirtinger.conjCLM_smul_I (d : ι → ℂ) :
    conjCLM (Complex.I • d) = -(Complex.I • conjCLM (ι := ι) d) := by
  funext I
  simp only [conjCLM_apply, Pi.star_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]
  ring
