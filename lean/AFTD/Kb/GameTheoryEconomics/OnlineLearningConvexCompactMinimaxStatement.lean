import AFTD.Prelude

/-!
# OnlineLearning.ConvexCompactMinimaxStatement

Topic: equilibria   Node: b725c5543c36

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.ConvexCompactMinimaxStatement`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For sets $X, Y \subseteq \bbr$ and a payoff function $f : \bbr \to \bbr \to \bbr$,
\texttt{OnlineLearning.ConvexCompactMinimaxStatement} is the proposition
\[
  \inf_{x \in X}\,\sup_{y \in Y}\,f(x,y)
  \;=\;
  \sup_{y \in Y}\,\inf_{x \in X}\,f(x,y).
\]
It is packaged as a named \texttt{Prop} so that intermediate lemmas can refer
to it while the proof is built up incrementally.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The conclusion of the convex-compact minimax theorem for a payoff `f` on `X × Y`: the upper value `inf_{x ∈ X} sup_{y ∈ Y} f x y` equals the lower value `sup_{y ∈ Y} inf_{x ∈ X} f x y`. [CBL06, Thm 7.1]. Deviation: specialized to subsets `X, Y ⊆ ℝ` (the source allows convex subsets of general topological vector spaces). This is packaged as a `Prop` so that the target can be referenced while the proof is developed in smaller lemmas. -/
def OnlineLearning.ConvexCompactMinimaxStatement (X Y : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  (⨅ x : X, ⨆ y : Y, f x y) = (⨆ y : Y, ⨅ x : X, f x y)
