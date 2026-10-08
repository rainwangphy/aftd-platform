import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3Satisfied
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.is3Satisfiable

Topic: np_completeness   Node: c81cd6201e65

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.is3Satisfiable`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-CNF formula $f$ is satisfiable if there exists an assignment $\alpha$ such
that $\alpha$ satisfies $f$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A 3-CNF formula is satisfiable if some assignment satisfies it. -/
def ThreeSATToClique.is3Satisfiable {V : Type} (f : Formula3 V) : Prop :=
  ∃ α : Assignment V, formula3Satisfied α f

-- =============================================================
-- Section 3. The conflict graph
-- =============================================================
