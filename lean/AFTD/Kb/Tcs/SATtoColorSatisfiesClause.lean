import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorSatisfiesLiteral
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.SatisfiesClause

Topic: np_completeness   Node: 550bf58bad05

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.SatisfiesClause`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under assignment $\mathrm{assign}$, a clause $c$ is satisfied if at least one
of its three literals evaluates to \texttt{true}:
\[
  \mathrm{SatisfiesClause}(\mathrm{assign}, c)
  \;=\;
  \mathrm{SatisfiesLiteral}(\mathrm{assign}, c.\ell_1)
  \;\vee\;
  \mathrm{SatisfiesLiteral}(\mathrm{assign}, c.\ell_2)
  \;\vee\;
  \mathrm{SatisfiesLiteral}(\mathrm{assign}, c.\ell_3).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def SATtoColor.SatisfiesClause {V : Type} (assign : V → Bool) (c : Clause V) : Bool :=
  SatisfiesLiteral assign c.l1 || SatisfiesLiteral assign c.l2 || SatisfiesLiteral assign c.l3
