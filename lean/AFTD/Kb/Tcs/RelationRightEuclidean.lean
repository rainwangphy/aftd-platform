import AFTD.Prelude

/-!
# Relation.RightEuclidean

Topic: computability   Node: 3c58a7006fc6

Provenance: formalization of a published result. Source: CSLib, `Relation.RightEuclidean`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation `r` is (right) Euclidean if `r a b` and `r a c` guarantee `r b c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation `r` is (right) Euclidean if `r a b` and `r a c` guarantee `r b c`. -/
class Relation.RightEuclidean (r : α → α → Prop) where
  rightEuclidean : r a b → r a c → r b c
