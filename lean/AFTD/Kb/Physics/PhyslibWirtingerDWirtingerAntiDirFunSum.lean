import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_fun_sum

Topic: classical_mechanics   Node: 0f333c56ae29

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_fun_sum`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-sum rule for `dWirtingerAntiDir`, `∂̄_v(∑ₐ Fₐ) = ∑ₐ ∂̄_v Fₐ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Finite-sum rule for `dWirtingerAntiDir`, `∂̄_v(∑ₐ Fₐ) = ∑ₐ ∂̄_v Fₐ`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (v : V) :
    dWirtingerAntiDir (fun p => ∑ a ∈ s, F a p) v u = ∑ a ∈ s, dWirtingerAntiDir (F a) v u := by
  simp only [dWirtingerAntiDir_apply, fderiv_fun_sum hF, sum_apply, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
