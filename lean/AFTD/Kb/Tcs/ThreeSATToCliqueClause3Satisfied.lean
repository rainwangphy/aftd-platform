import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueEvalLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3

/-!
# ThreeSATToClique.clause3Satisfied

Topic: np_completeness   Node: 5baafa12af1f

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.clause3Satisfied`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-clause $c$ is satisfied by $\alpha$ if at least one of its three literals
$c.l_1$, $c.l_2$, $c.l_3$ evaluates to true under $\alpha$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A 3-clause is satisfied if at least one of its three literals is true. -/
def ThreeSATToClique.clause3Satisfied {V : Type} (α : Assignment V) (c : Clause3 V) : Prop :=
  evalLiteral α c.l1 ∨ evalLiteral α c.l2 ∨ evalLiteral α c.l3
