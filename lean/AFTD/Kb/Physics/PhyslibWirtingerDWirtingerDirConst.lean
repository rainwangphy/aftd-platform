import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply

/-!
# Physlib.Wirtinger.dWirtingerDir_const

Topic: classical_mechanics   Node: 10473b15526f

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_const`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Constants have zero holomorphic directional Wirtinger derivative, `∂_v c = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Constants have zero holomorphic directional Wirtinger derivative, `∂_v c = 0`. -/
@[simp] lemma Physlib.Wirtinger.dWirtingerDir_const (c : ℂ) (v u : V) :
    dWirtingerDir (fun _ : V => c) v u = 0 := by simp [dWirtingerDir_apply]
