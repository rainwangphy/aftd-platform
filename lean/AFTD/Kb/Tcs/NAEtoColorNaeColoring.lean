import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAEclause
import AFTD.Kb.Tcs.NAEtoColorOutputVertex
import AFTD.Kb.Tcs.NAEtoColorClauseNodeColor

/-!
# NAEtoColor.naeColoring

Topic: np_completeness   Node: 77f1ca586d3c

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.naeColoring`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Boolean assignment $\mathit{assign} : V \to \mathtt{Bool}$, defines a
coloring of all vertices of the reduction graph by:
$\mathtt{groundNode} \mapsto 0$;
$\mathtt{varNode}\;v \mapsto 1$ if $\mathit{assign}(v) = \mathtt{true}$, else $2$;
$\mathtt{clauseNode}\;c\;k \mapsto
\texttt{NAEtoColor.clauseNodeColor}\;(\mathit{assign}(c.v_0))\;(\mathit{assign}(c.v_1))\;(\mathit{assign}(c.v_2))\;k$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Coloring of entire simple graph obtained via reduction from NAE-SAT. Coloring constructed from NAE-SAT assignment. • groundNode ↦ 0 • varNode v ↦ 1 if assign v = true, else 2 • clauseNode c k ↦ clauseNodeColor (assign values of the 3 variables) -/
def NAEtoColor.naeColoring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .groundNode => 0
  | .varNode v => if assign v then 1 else 2
  | .clauseNode c k => clauseNodeColor (assign c.v0) (assign c.v1) (assign c.v2) k
