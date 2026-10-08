import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAEclause

/-!
# NAEtoColor.SatisfiesClause

Topic: np_completeness   Node: 5747c465927d

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.SatisfiesClause`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Boolean assignment $\mathit{assign} : V \to \mathtt{Bool}$ and a
Not-All-Equal clause $c$ with three variables $c.v_0, c.v_1, c.v_2$,
$\texttt{NAEtoColor.SatisfiesClause}$ returns $\mathtt{true}$ if and only if
the three assigned values are \emph{not} all equal, i.e.\ at least two of
$\mathit{assign}(c.v_0)$, $\mathit{assign}(c.v_1)$, $\mathit{assign}(c.v_2)$
differ.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Evaluate a Not-All-Equal clause -/
def NAEtoColor.SatisfiesClause {V : Type} (assign : V → Bool) (c : NAEclause V) : Bool :=
  (
    assign c.v0 ≠ assign c.v1 ||
    assign c.v0 ≠ assign c.v2 ||
    assign c.v1 ≠ assign c.v2
  )
