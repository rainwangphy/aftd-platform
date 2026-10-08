import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.Literal

Topic: np_completeness   Node: 3bb05d0fd954

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.Literal`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A literal for switching-lemma formulas: a variable $\mathtt{var} : \mathrm{Fin}\,n$
with a negation flag $\mathtt{neg} : \mathrm{Bool}$ (true = negated literal).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
inductive SATtoColor.Literal (V : Type) | pos (v : V)
| neg (v : V)
