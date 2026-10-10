import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmToLinear1
import AFTD.Kb.Physics.TriLinearSymmToLinear1Apply

/-!
# TriLinearSymm.map_sum₁

Topic: classical_mechanics   Node: 7ca81c6aaa6f

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_sum₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_sum₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_sum₁ {n : ℕ} (f : TriLinearSymm V) (S : Fin n → V) (T : V) (L : V) :
    f (∑ i, S i) T L = ∑ i, f (S i) T L := by
  rw [f.toLinear₁_apply, map_sum]
  rfl
