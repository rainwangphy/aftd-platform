import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.OutputVertex

Topic: np_completeness   Node: 088ebe5645e3

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.OutputVertex`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The vertex set of the reduction graph is the inductive type
$\mathrm{OutputVertex}(V)$ with three constructors:
\begin{itemize}
  \item $\mathrm{palette}(p)$ for $p : \mathrm{Fin}\,3$ --- the three special
        palette nodes (Base $= 0$, True $= 1$, False $= 2$) forming a triangle
        that fixes color semantics;
  \item $\mathrm{literalNode}(\ell)$ --- one node per literal over $V$
        (positive and negative occurrences are separate nodes);
  \item $\mathrm{clauseGadget}(c, k)$ for $k : \mathrm{Fin}\,6$ --- six
        internal nodes per clause $c$ encoding the OR constraint.
\end{itemize}
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Vertex set for reduction from 3-SAT to 3-COLORING. • palette – the special triangle fixing color semantics (Base=0, T=1, F=2). • literalNode – one node per literal (pos and neg are separate nodes). • clauseGadget – six internal nodes per clause encoding the OR constraint. -/
inductive SATtoColor.OutputVertex (V : Type) | palette (p : Fin 3)
| literalNode (l : Literal V)
| clauseGadget (c : Clause V) (idx : Fin 6)
