import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.TriLinearSymmMapSum1

/-!
# TriLinearSymm.map_sum₂

Topic: classical_mechanics   Node: 51ab02a0bd86

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_sum₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_sum₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_sum₂ {n : ℕ} (f : TriLinearSymm V) (S : Fin n → V) (T : V) (L : V) :
    f T (∑ i, S i) L = ∑ i, f T (S i) L := by
  rw [swap₁, map_sum₁]
  refine Fintype.sum_congr _ _ fun _ ↦ swap₁ f (S _) T L
