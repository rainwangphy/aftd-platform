import AFTD.Prelude

/-!
# NAEtoColor.NAEclause

Topic: np_completeness   Node: 07a17d824f65

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.NAEclause`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Not-All-Equal Clause
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A Not-All-Equal Clause -/
structure NAEtoColor.NAEclause (V : Type) where
  v0 : V
  v1 : V
  v2 : V
