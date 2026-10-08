import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorSatisfiesLiteral
import AFTD.Kb.Tcs.SATtoColorClauseGadgetColor
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.sat3Coloring

Topic: np_completeness   Node: f015e8cda2cc

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.sat3Coloring`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a satisfying assignment $\mathrm{assign} : V \to \mathrm{Bool}$, the
function $\mathrm{sat3Coloring}(\mathrm{assign})$ maps every vertex of
$\mathrm{OutputVertex}(V)$ to a color in $\mathrm{Fin}\,3$: palette node $p$
gets color $p$; a positive (resp.\ negative) literal node for variable $v$
gets color $1$ (True) if $\mathrm{assign}(v) = \texttt{true}$ and color $2$
(False) otherwise (resp.\ the reverse); clause gadget node $(c, k)$ gets
$\mathrm{clauseGadgetColor}$ applied to the truth values of $c$'s three
literals.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Coloring constructed from a satisfying assignment. -/
def SATtoColor.sat3Coloring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .palette p => p
  | .literalNode (.pos v) => if assign v then 1 else 2
  | .literalNode (.neg v) => if assign v then 2 else 1
  | .clauseGadget c k =>
      clauseGadgetColor (SatisfiesLiteral assign c.l1)
                        (SatisfiesLiteral assign c.l2)
                        (SatisfiesLiteral assign c.l3) k
