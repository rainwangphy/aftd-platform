import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment

/-!
# ThreeSATToClique.evalLiteral

Topic: np_completeness   Node: c9c954c0d06c

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.evalLiteral`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a truth assignment $\alpha : V \to \mathrm{Prop}$, the evaluation of a
literal $\ell$ under $\alpha$ is $\alpha(v)$ when $\ell = \texttt{pos}\,v$ and
$\neg\,\alpha(v)$ when $\ell = \texttt{neg}\,v$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The truth value of a literal under a given assignment. -/
def ThreeSATToClique.evalLiteral {V : Type} (α : Assignment V) : Literal V → Prop
  | .pos v => α v
  | .neg v => ¬(α v)
