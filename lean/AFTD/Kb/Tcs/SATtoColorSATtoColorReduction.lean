import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorIs3Colorable
import AFTD.Kb.Tcs.SATtoColorIsSatisfiable
import AFTD.Kb.Tcs.SATtoColorReductionGraph
import AFTD.Kb.Tcs.SATtoColorSATtoColorCompleteness
import AFTD.Kb.Tcs.SATtoColorSATtoColorSoundness
import AFTD.Kb.Tcs.SATtoColorSat3
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.SATtoColorReduction

Topic: np_completeness   Node: 0499fec5ca96

Provenance: formalization of a published result. Source: Correctness of the 3-SAT to 3-coloring reduction, as formalized in TCSlib (`SATtoColor.SATtoColorReduction`). Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Correctness of the 3-SAT to 3-coloring reduction. Let $f$ be a 3-SAT instance over a variable type $V$: a list of clauses, each clause an
ordered triple of literals, where a literal is a positive or a negative occurrence of a
variable in $V$. Then $f$ is satisfiable — some Boolean assignment $V \to
\{\mathrm{true}, \mathrm{false}\}$ makes every clause in $f$ true — if and only if the
reduction graph associated to $f$ is 3-colorable, that is, admits a proper coloring by
three colors.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Main theorem: 3-SAT is satisfiable iff the reduction graph is 3-colorable. -/
theorem SATtoColor.SATtoColorReduction {V : Type} (f : Sat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (SATtoColorCompleteness f) (SATtoColorSoundness f)
