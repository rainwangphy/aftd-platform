import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.V

/-!
# SATtoColor.SatisfiesLiteral

Topic: np_completeness   Node: 8f1955141881

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.SatisfiesLiteral`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Boolean assignment $\mathrm{assign} : V \to \mathrm{Bool}$, the
function $\texttt{SATtoColor.SatisfiesLiteral}$ evaluates a literal: a positive
literal $\mathrm{pos}(v)$ evaluates to $\mathrm{assign}(v)$, and a negative
literal $\mathrm{neg}(v)$ evaluates to $\neg\,\mathrm{assign}(v)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def SATtoColor.SatisfiesLiteral {V : Type} (assign : V → Bool) : Literal V → Bool
  | Literal.pos v => assign v
  | Literal.neg v => !(assign v)
