import AFTD.Prelude

/-!
# Relation.LeftEuclidean

Topic: computability   Node: ebc5349415d7

Provenance: formalization of a published result. Source: CSLib, `Relation.LeftEuclidean`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation `r` is (left) Euclidean if `r a c` and `r b c` guarantee `r a b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation `r` is (left) Euclidean if `r a c` and `r b c` guarantee `r a b`. -/
class Relation.LeftEuclidean (r : α → α → Prop) where
  leftEuclidean {a b c} : r a c → r b c → r a b
