import AFTD.Prelude

/-!
# ProbabilisticTheory.Effect

Topic: quantum_mechanics   Node: 10176c48a5f2

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.Effect`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Effect/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A bounded measurement outcome.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A bounded measurement outcome. -/
abbrev ProbabilisticTheory.Effect (E : Type*) [PartialOrder E] [One E] [Zero E] := Set.Icc (0 : E) 1
