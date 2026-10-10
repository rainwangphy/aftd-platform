import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryPosCone

/-!
# ProbabilisticTheory.PosCone.instModule

Topic: quantum_mechanics   Node: dc1bff776fb4

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.PosCone.instModule`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Cone.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The positive cone carries a nonnegative-real scalar action.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
open scoped NNReal in
variable {E : Type*} [OrderedVectorSpace E] in
/-- The positive cone carries a nonnegative-real scalar action. -/
instance ProbabilisticTheory.PosCone.instModule : Module ℝ≥0 (PosCone E) :=
  inferInstanceAs (Module {c : ℝ // 0 ≤ c} (PointedCone.positive ℝ E))
