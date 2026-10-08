import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAEclause

/-!
# NAEtoColor.NAESat3

Topic: np_completeness   Node: 91627d7d7749

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.NAESat3`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A NAE-SAT instance over variable type $V$ is defined as a list of NAE clauses,
i.e.\ $\texttt{NAEtoColor.NAESat3}\;V = \mathtt{List}\;(\mathtt{NAEclause}\;V)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A NAE-SAT instance is a list of NAE clauses. -/
abbrev NAEtoColor.NAESat3 (V : Type) := List (NAEclause V)
