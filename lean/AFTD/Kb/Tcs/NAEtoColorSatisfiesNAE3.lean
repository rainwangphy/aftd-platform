import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorSatisfiesClause

/-!
# NAEtoColor.SatisfiesNAE3

Topic: np_completeness   Node: d93147291d5b

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.SatisfiesNAE3`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given an assignment $\mathit{assign} : V \to \mathtt{Bool}$ and a NAE-SAT
instance $f$, $\texttt{NAEtoColor.SatisfiesNAE3}$ returns $\mathtt{true}$ if
and only if every clause in $f$ is satisfied by $\mathit{assign}$
(i.e.\ $\texttt{NAEtoColor.SatisfiesClause}$ holds for each clause).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Returns `true` if the assignment satisfies all clauses. -/
def NAEtoColor.SatisfiesNAE3 {V : Type} (assign : V → Bool) (f : NAESat3 V) : Bool :=
  f.all (SatisfiesClause assign)
