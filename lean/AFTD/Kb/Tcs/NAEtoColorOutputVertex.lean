import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAEclause

/-!
# NAEtoColor.OutputVertex

Topic: np_completeness   Node: 4a4b3f67e2fc

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.OutputVertex`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The vertex set of the reduction graph is an inductive type with three
constructors:
\begin{itemize}
  \item $\mathtt{groundNode}$ --- a single ground vertex (colored ``neutral'');
  \item $\mathtt{varNode}\;v$ --- one vertex per variable $v \in V$;
  \item $\mathtt{clauseNode}\;c\;k$ --- three internal gadget vertices
        ($k \in \mathrm{Fin}\,3$) for each clause $c$.
\end{itemize}
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Vertex set for reduction from NAE-SAT to 3-COLORING. We map the input variables to output vertices using an inductive type. This cleanly separates the three kinds of vertices without any integer indexing: • groundNode – 1 ground node, who color is 0 (assume True = 1, False = 2). • varNode – 1 node per variable. • clauseNode – 3 internal nodes per clause that encode the NAE constraint. -/
inductive NAEtoColor.OutputVertex (V : Type) | groundNode                                 -- ground vertex colored "neutral"
| varNode (v : V)                            -- one node per variable
| clauseNode (c : NAEclause V) (idx : Fin 3) -- 3 nodes per clause
