import AFTD.Prelude
import AFTD.Kb.Tcs.CslibInfVSet

/-!
# Cslib.Selection

Topic: combinatorics   Node: e21359abc5b9

Provenance: formalization of a published result. Source: CSLib, `Cslib.Selection`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `Selection` consists of an `InfVSet`, a vertex, and a color.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
/-- A `Selection` consists of an `InfVSet`, a vertex, and a color. -/
structure Cslib.Selection (Vertex Color : Type*) where
  /-- An infinite set of vertices. -/
  vs : InfVSet Vertex
  /-- A vertex. -/
  v : Vertex
  /-- A color. -/
  c : Color
