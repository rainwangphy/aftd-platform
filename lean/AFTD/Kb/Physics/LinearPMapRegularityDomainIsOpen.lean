import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapRegularityDomain
import AFTD.Kb.Physics.LinearPMapIsLowerBound
import AFTD.Kb.Physics.LinearPMapBallSubsetRegularityDomain

/-!
# LinearPMap.regularityDomain_isOpen

Topic: quantum_mechanics   Node: 98645b05079d

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.regularityDomain_isOpen`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The regularity domain is an open set.
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
/-- The regularity domain is an open set. -/
lemma LinearPMap.regularityDomain_isOpen (T : H →ₗ.[ℂ] H) : IsOpen T.regularityDomain :=
  isOpen_iff.mpr fun _ ⟨c, hc, h⟩ ↦ ⟨c, hc, ball_subset_regularityDomain h⟩
