import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapRegularityDomain
import AFTD.Kb.Physics.LinearPMapIsLowerBound
import AFTD.Kb.Physics.LinearPMapIsLowerBoundNeg

/-!
# LinearPMap.regularityDomain_neg

Topic: quantum_mechanics   Node: fccae8afa966

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.regularityDomain_neg`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.regularityDomain_neg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
@[simp]
lemma LinearPMap.regularityDomain_neg (T : H →ₗ.[ℂ] H) : (-T).regularityDomain = -T.regularityDomain := by
  ext z
  constructor
  · exact fun ⟨c, hc, h_bound⟩ ↦ ⟨c, hc, neg_neg T ▸ isLowerBound_neg h_bound⟩
  · exact fun ⟨c, hc, h_bound⟩ ↦ ⟨c, hc, neg_neg z ▸ isLowerBound_neg h_bound⟩
