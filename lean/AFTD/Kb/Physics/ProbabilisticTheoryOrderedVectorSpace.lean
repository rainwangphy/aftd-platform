import AFTD.Prelude

/-!
# ProbabilisticTheory.OrderedVectorSpace

Topic: quantum_mechanics   Node: ace35e99a385

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderedVectorSpace`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ordered real vector space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An ordered real vector space. -/
class ProbabilisticTheory.OrderedVectorSpace (E : Type*) extends AddCommGroup E, PartialOrder E, Module ℝ E,
    IsOrderedAddMonoid E, PosSMulMono ℝ E
