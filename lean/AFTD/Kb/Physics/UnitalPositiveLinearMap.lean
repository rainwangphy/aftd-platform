import AFTD.Prelude

/-!
# UnitalPositiveLinearMap

Topic: quantum_mechanics   Node: 627560b122de

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A positive linear map preserving `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A positive linear map preserving `1`. -/
@[ext]
structure UnitalPositiveLinearMap (R E F : Type*) [Semiring R]
    [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
    [Module R E] [Module R F] [One E] [One F] extends E →ₚ[R] F, OneHom E F attribute [nolint docBlame] UnitalPositiveLinearMap.toOneHom
