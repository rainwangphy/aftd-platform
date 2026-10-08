import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral

/-!
# ThreeSATToClique.literalsConflict

Topic: np_completeness   Node: e7fa740b241a

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.literalsConflict`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two literals $l_1$ and $l_2$ \emph{conflict} if one is the positive and the other
the negative occurrence of the same variable, i.e.\ $l_1 = \texttt{pos}\,v$ and
$l_2 = \texttt{neg}\,v$ (or vice versa) for some $v$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Two literals *conflict* if one is the positive and the other the negative occurrence of the same variable. -/
def ThreeSATToClique.literalsConflict {V : Type} (l1 l2 : Literal V) : Prop :=
  match l1, l2 with
  | .pos v1, .neg v2 => v1 = v2
  | .neg v1, .pos v2 => v1 = v2
  | _, _ => False
