import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun

/-!
# BiLinearSymm.map_sum₂

Topic: classical_mechanics   Node: 63c1fea9cd76

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.map_sum₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.map_sum₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.map_sum₂ {n : ℕ} (f : BiLinearSymm V) (S : Fin n → V) (T : V) :
    f T (∑ i, S i) = ∑ i, f T (S i) := map_sum (f T) S Finset.univ
