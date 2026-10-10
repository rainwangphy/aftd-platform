import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapRegularityDomain
import AFTD.Kb.Physics.LinearPMapRegularityDomainAntitone
import AFTD.Kb.Physics.LinearPMapIsLowerBound
import AFTD.Kb.Physics.LinearPMapIsLowerBoundClosure

/-!
# LinearPMap.regularityDomain_closure

Topic: quantum_mechanics   Node: e3368db277e1

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.regularityDomain_closure`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`T` and `T.closure` have the same regularity domain.
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
/-- `T` and `T.closure` have the same regularity domain. -/
lemma LinearPMap.regularityDomain_closure (T : H →ₗ.[ℂ] H) :
    T.closure.regularityDomain = T.regularityDomain :=
  eq_of_le_of_ge (regularityDomain_antitone T.le_closure)
    fun _ ⟨c, hc, h⟩ ↦ ⟨c, hc, isLowerBound_closure h⟩
