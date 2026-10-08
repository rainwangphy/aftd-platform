import AFTD.Prelude

/-!
# ThreeSATToClique.Literal

Topic: np_completeness   Node: 97f717cf3f5f

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.Literal`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A literal for switching-lemma formulas: a variable $\mathtt{var} : \mathrm{Fin}\,n$
with a negation flag $\mathtt{neg} : \mathrm{Bool}$ (true = negated literal).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A literal is either a positive or negative occurrence of a variable. -/
inductive ThreeSATToClique.Literal (V : Type) | pos (v : V)
  | neg (v : V)
