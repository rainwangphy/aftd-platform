import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmMapSum1
import AFTD.Kb.Physics.TriLinearSymmMapSum2
import AFTD.Kb.Physics.TriLinearSymmMapSum3

/-!
# TriLinearSymm.map_sum₁₂₃

Topic: classical_mechanics   Node: 84f7f7ff210f

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_sum₁₂₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_sum₁₂₃
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_sum₁₂₃ {n1 n2 n3 : ℕ} (f : TriLinearSymm V) (S : Fin n1 → V)
    (T : Fin n2 → V) (L : Fin n3 → V) :
    f (∑ i, S i) (∑ i, T i) (∑ i, L i) = ∑ i, ∑ k, ∑ l, f (S i) (T k) (L l) := by
  rw [map_sum₁]
  apply Fintype.sum_congr _ _ fun _ ↦ ?_
  rw [map_sum₂]
  exact Fintype.sum_congr _ _ fun _ ↦ map_sum₃ f L (S _) (T _)
