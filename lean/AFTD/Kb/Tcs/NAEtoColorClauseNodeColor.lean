import AFTD.Prelude

/-!
# NAEtoColor.clauseNodeColor

Topic: np_completeness   Node: 2f6737714b2b

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.clauseNodeColor`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given three Boolean values $a, b, c$ (the truth values of a clause's three
literals) and an index $k \in \mathrm{Fin}\,3$, returns the color in
$\mathrm{Fin}\,3$ assigned to the $k$-th internal clause-gadget node.
The coloring is chosen so that all three gadget nodes receive distinct colors
whenever $(a, b, c)$ is a NAE-satisfying assignment; if the assignment is
not NAE-satisfying, all gadget nodes are colored $0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Coloring of clause nodes obtained via reduction from NAE-SAT. Given the boolean values of the three literals in a clause, assigns colors to the three internal clause-gadget nodes. We do not assume that the clause is in the NAE-SAT instance. If the variables do not satisfy the Not-All-Equal clause, we color everything 0. This is a valid coloring since there are no edges between clause nodes in that case, and all variable nodes are colored either 1 or 2. -/
def NAEtoColor.clauseNodeColor (a b c : Bool) (k : Fin 3) : Fin 3 :=
  match a, b, c with
  | true,  true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | true,  false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | false, true,  true  => match k with | 0 => 1 | 1 => 0 | 2 => 2
  | true,  false, false => match k with | 0 => 2 | 1 => 0 | 2 => 1
  | false, true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | false, false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | _,     _,     _     => 0  -- (non-NAE cases have no clause-clause edges)
