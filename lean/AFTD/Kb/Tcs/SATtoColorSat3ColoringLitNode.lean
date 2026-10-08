import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorSatisfiesLiteral
import AFTD.Kb.Tcs.SATtoColorSat3Coloring
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.sat3Coloring_litNode

Topic: np_completeness   Node: 0743542e47f5

Provenance: helper lemma. TCSlib, `SATtoColor.sat3Coloring_litNode`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Color of a literal node. Fix a variable type $V$ and a Boolean assignment $\alpha : V \to \{\text{true},
\text{false}\}$, and consider the coloring of the reduction graph induced by $\alpha$,
which sends each vertex to a color in $\{0, 1, 2\}$ (with $1$ standing for True and $2$
for False). For every literal $\ell$ over $V$, the literal node of $\ell$ receives color
$1$ if $\ell$ is satisfied by $\alpha$, and color $2$ otherwise:
\[
  \text{color of the literal node of } \ell
  \;=\;
\begin{cases} 1 & \text{if $\ell$ is satisfied by $\alpha$,}\\ 2 &
\text{otherwise.}\end{cases}
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma SATtoColor.sat3Coloring_litNode {V : Type} (assign : V → Bool) (l : Literal V) :
    sat3Coloring assign (.literalNode l) = if SatisfiesLiteral assign l then 1 else 2 := by
  match l with
  | .pos v => simp [sat3Coloring, SatisfiesLiteral]; rfl
  | .neg v =>
    show (if assign v then (2 : Fin 3) else 1) = if !assign v then 1 else 2
    match assign v with | true => rfl | false => rfl
