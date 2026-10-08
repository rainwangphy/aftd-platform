import AFTD.Prelude

/-!
# OnlineLearning.minimaxSublevel

Topic: equilibria   Node: 8d8457eb24d2

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.minimaxSublevel`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a set $X \subseteq \bbr$, a payoff function $f$, a column point $y$, and
a threshold $c \in \bbr$, the \emph{minimax sublevel set} is
\[
  \mathrm{sublevel}(X,f,y,c) \;=\; X \cap \{x \in \bbr : f(x,y) \leq c\}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The sublevel set `{x ∈ X | f x y ≤ c}`: the subset of the row set `X` where the payoff against the column point `y` is at most `c`. -/
def OnlineLearning.minimaxSublevel (X : Set ℝ) (f : ℝ → ℝ → ℝ) (y c : ℝ) : Set ℝ :=
  X ∩ {x | f x y ≤ c}
