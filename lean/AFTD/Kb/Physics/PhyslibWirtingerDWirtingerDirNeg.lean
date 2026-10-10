import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst

/-!
# Physlib.Wirtinger.dWirtingerDir_neg

Topic: classical_mechanics   Node: d14a40fe810c

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_neg`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`dWirtingerDir` of a negated function, `∂_v(−g) = −∂_v g`. Holds with no differentiability hypothesis, since `fderiv` of a negation is unconditional.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- `dWirtingerDir` of a negated function, `∂_v(−g) = −∂_v g`. Holds with no differentiability hypothesis, since `fderiv` of a negation is unconditional. -/
@[simp] lemma Physlib.Wirtinger.dWirtingerDir_neg (g : V → ℂ) (v u : V) :
    dWirtingerDir (fun p => -(g p)) v u = -(dWirtingerDir g v u) := by
  simp only [dWirtingerDir_apply, fderiv_fun_neg, _root_.neg_apply]
  ring
