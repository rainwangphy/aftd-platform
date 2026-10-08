import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorSatisfiesNAE3

/-!
# NAEtoColor.IsSatisfiable

Topic: np_completeness   Node: bb857f0ffdf8

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.IsSatisfiable`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A NAE-SAT instance $f$ over variable type $V$ is \emph{satisfiable} if there
exists a Boolean assignment $\mathit{assign} : V \to \mathtt{Bool}$ such that
$\texttt{NAEtoColor.SatisfiesNAE3}\;\mathit{assign}\;f = \mathtt{true}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The satisfiability property for a NAE-SAT instance. -/
noncomputable def NAEtoColor.IsSatisfiable {V : Type} (f : NAESat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesNAE3 assign f = true

-- Some examples to test definitions:
