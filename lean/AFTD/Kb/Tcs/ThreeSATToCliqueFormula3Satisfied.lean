import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3Satisfied
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3

/-!
# ThreeSATToClique.formula3Satisfied

Topic: np_completeness   Node: 08b720bb4d9d

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.formula3Satisfied`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-CNF formula $f$ is satisfied by $\alpha$ if every 3-clause $c \in f$ is
satisfied by $\alpha$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A 3-CNF formula is satisfied if every 3-clause is satisfied. -/
def ThreeSATToClique.formula3Satisfied {V : Type} (α : Assignment V) (f : Formula3 V) : Prop :=
  ∀ c ∈ f, clause3Satisfied α c
