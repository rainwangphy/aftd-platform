import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_neg

Topic: classical_mechanics   Node: e8fe84e725b5

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_neg`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`dWirtingerAntiDir` of a negated function, `∂̄_v(−g) = −∂̄_v g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- `dWirtingerAntiDir` of a negated function, `∂̄_v(−g) = −∂̄_v g`. -/
@[simp] lemma Physlib.Wirtinger.dWirtingerAntiDir_neg (g : V → ℂ) (v u : V) :
    dWirtingerAntiDir (fun p => -(g p)) v u = -(dWirtingerAntiDir g v u) := by
  simp only [dWirtingerAntiDir_apply, fderiv_fun_neg, _root_.neg_apply]
  ring
