import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3

/-!
# ThreeSATToClique.Formula3

Topic: np_completeness   Node: 9880b3b820fd

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.Formula3`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-CNF formula over $V$ is a list of 3-clauses, representing their conjunction.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A 3-CNF formula is a conjunction of 3-clauses. -/
abbrev ThreeSATToClique.Formula3 (V : Type) := List (Clause3 V)
