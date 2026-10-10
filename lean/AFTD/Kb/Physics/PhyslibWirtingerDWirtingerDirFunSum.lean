import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_fun_sum

Topic: classical_mechanics   Node: 480a795d5296

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_fun_sum`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-sum rule for `dWirtingerDir`, `∂_v(∑ₐ Fₐ) = ∑ₐ ∂_v Fₐ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Finite-sum rule for `dWirtingerDir`, `∂_v(∑ₐ Fₐ) = ∑ₐ ∂_v Fₐ`. -/
lemma Physlib.Wirtinger.dWirtingerDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (v : V) :
    dWirtingerDir (fun p => ∑ a ∈ s, F a p) v u = ∑ a ∈ s, dWirtingerDir (F a) v u := by
  simp only [dWirtingerDir_apply, fderiv_fun_sum hF, sum_apply, mul_sub, Finset.mul_sum,
    Finset.sum_sub_distrib]
