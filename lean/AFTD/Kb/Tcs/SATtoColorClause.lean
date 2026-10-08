import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.Clause

Topic: np_completeness   Node: 95cf6b75f6b4

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.Clause`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{clause} over a variable type $V$ is a structure bundling exactly three
literals $\ell_1, \ell_2, \ell_3 : \mathrm{Literal}\,V$.  Each literal is
either a positive or a negative occurrence of some variable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
structure SATtoColor.Clause (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V
