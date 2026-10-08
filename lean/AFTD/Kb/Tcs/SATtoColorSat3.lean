import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.Sat3

Topic: np_completeness   Node: a7e744293cdb

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.Sat3`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-SAT instance over variable type $V$ is defined as a list of clauses,
i.e.\ $\mathrm{Sat3}(V) := \mathrm{List}(\mathrm{Clause}\,V)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
abbrev SATtoColor.Sat3 (V : Type) := List (Clause V)
