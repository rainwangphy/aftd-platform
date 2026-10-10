import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapRegularityDomain
import AFTD.Kb.Physics.LinearPMapIsLowerBound
import AFTD.Kb.Physics.LinearPMapIsLowerBoundOfLeftLe

/-!
# LinearPMap.regularityDomain_antitone

Topic: quantum_mechanics   Node: d6043765a168

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.regularityDomain_antitone`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`T ≤ T'` implies `T'.regularityDomain ⊆ T.regularityDomain`.
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
/-- `T ≤ T'` implies `T'.regularityDomain ⊆ T.regularityDomain`. -/
lemma LinearPMap.regularityDomain_antitone : Antitone (regularityDomain (H := H)) :=
  fun _ _ hle _ ⟨c, hc, h⟩ ↦ ⟨c, hc, isLowerBound_of_left_le hle h⟩
