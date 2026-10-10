import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.PosCone

Topic: quantum_mechanics   Node: c744fc6b690d

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.PosCone`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Cone.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The positive pointed cone of an ordered real module.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped NNReal in
/-- The positive pointed cone of an ordered real module. -/
abbrev ProbabilisticTheory.PosCone (E : Type*) [OrderedVectorSpace E] : PointedCone ℝ E :=
  PointedCone.positive ℝ E
