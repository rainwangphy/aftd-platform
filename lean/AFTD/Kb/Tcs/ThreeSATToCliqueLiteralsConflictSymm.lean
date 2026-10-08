import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflict

/-!
# ThreeSATToClique.literalsConflict_symm

Topic: np_completeness   Node: fd1f784415ab

Provenance: helper lemma. TCSlib, `ThreeSATToClique.literalsConflict_symm`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Symmetry of literal conflict. Call two literals over a variable set *conflicting* when one is the positive and the
other the negative occurrence of one and the same variable. For any two literals $l_1$
and $l_2$, $l_1$ and $l_2$ conflict if and only if $l_2$ and $l_1$ conflict; that is,
the conflict relation is symmetric.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- `literalsConflict` is symmetric. -/
theorem ThreeSATToClique.literalsConflict_symm {V : Type} (l1 l2 : Literal V) :
    literalsConflict l1 l2 ↔ literalsConflict l2 l1 := by
  cases l1 <;> cases l2 <;> simp only [literalsConflict]
  · exact eq_comm
  · exact eq_comm
