import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral

/-!
# ThreeSATToClique.Clause3

Topic: np_completeness   Node: e4756adf9944

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.Clause3`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-clause over $V$ is a structure with exactly three literals $l_1, l_2, l_3 :
\mathtt{Literal}\,V$, representing a disjunction of precisely three literals.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A 3-clause is a disjunction of exactly three literals. -/
structure ThreeSATToClique.Clause3 (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V
