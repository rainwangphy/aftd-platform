import AFTD.Prelude

/-!
# Cslib.InfVSet

Topic: combinatorics   Node: 31e764222146

Provenance: formalization of a published result. Source: CSLib, `Cslib.InfVSet`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `InfVSet` consists of a set of vertices and a proof that the set is infinite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
/-- An `InfVSet` consists of a set of vertices and a proof that the set is infinite. -/
structure Cslib.InfVSet (Vertex : Type*) where
  /-- A set of vertices. -/
  set : Set Vertex
  /-- A proof that `set` is infinite. -/
  inf : set.Infinite
