import AFTD.Prelude

/-!
# Physlib.MultiIndex

Topic: classical_mechanics   Node: 12d68fa24d13

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multi-index on `d` source coordinates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
/-- A multi-index on `d` source coordinates. -/
structure Physlib.MultiIndex (d : ℕ) where
  /-- The coordinates of the multi-index. -/
  toFun : Fin d → ℕ
deriving DecidableEq
