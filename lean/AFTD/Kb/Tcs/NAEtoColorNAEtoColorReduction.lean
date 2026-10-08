import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorIs3Colorable
import AFTD.Kb.Tcs.NAEtoColorIsSatisfiable
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorNAEtoColorCompleteness
import AFTD.Kb.Tcs.NAEtoColorNAEtoColorSoundness
import AFTD.Kb.Tcs.NAEtoColorReductionGraph
import AFTD.Kb.Tcs.V

/-!
# NAEtoColor.NAEtoColorReduction

Topic: np_completeness   Node: 19d470b41b21

Provenance: formalization of a published result. Source: Correctness of the NAE-SAT to 3-coloring reduction, as formalized in TCSlib (`NAEtoColor.NAEtoColorReduction`). Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Correctness of the NAE-SAT to 3-coloring reduction. Let $f$ be a NAE-SAT instance over a variable type $V$, and let $\Gamma(f)$ denote its
reduction graph, the simple graph built from $f$ as described above (a ground vertex
joined to every variable vertex, each variable vertex joined to the clause-gadget
vertices for the clauses in which it occurs, and the three gadget vertices of each
clause joined pairwise into a triangle). Then $f$ is satisfiable if and only if
$\Gamma(f)$ is 3-colorable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Main reduction theorem from NAE-SAT to 3-Coloring. -/
theorem NAEtoColor.NAEtoColorReduction {V : Type} (f : NAESat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (NAEtoColorCompleteness f) (NAEtoColorSoundness f)
