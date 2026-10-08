import AFTD.Prelude

/-!
# OnlineLearning.ConvexCompactMinimaxHypotheses

Topic: equilibria   Node: be9c0ccc7130

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.ConvexCompactMinimaxHypotheses`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A structure bundling the assumptions of Cesa-Bianchi--Lugosi Theorem~7.1
for $f : \bbr \to \bbr \to \bbr$ on sets $X, Y \subseteq \bbr$: both sets
are nonempty, $X$ is compact and convex, $Y$ is convex, $f(\cdot,y)$ is
continuous and convex on $X$ for every $y \in Y$, $f(x,\cdot)$ is concave on
$Y$ for every $x \in X$, and $f$ is bounded above and below on $X \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
variable (X Y : Set ℝ) (f : ℝ → ℝ → ℝ) in
/-- The hypotheses of the convex-compact minimax theorem [CBL06, Thm 7.1], specialized to `ℝ`: `X` and `Y` are nonempty convex subsets of `ℝ`, `X` is compact, the payoff `f` is continuous and convex in the row variable for each column point, concave in the column variable for each row point, and bounded on `X × Y`. Deviation: `X, Y ⊆ ℝ`, and the continuity and boundedness requirements are made explicit fields (the source states them in prose). -/
structure OnlineLearning.ConvexCompactMinimaxHypotheses : Prop where
  /-- The row set is nonempty. -/
  X_nonempty : X.Nonempty
  /-- The column set is nonempty. -/
  Y_nonempty : Y.Nonempty
  /-- Compactness of the row set is used for the finite-intersection argument. -/
  X_compact : IsCompact X
  /-- The row set is convex, so mixtures of row points stay in `X`. -/
  X_convex : Convex ℝ X
  /-- The column set is convex, so mixtures of column points stay in `Y`. -/
  Y_convex : Convex ℝ Y
  /-- For each column point, the payoff is continuous in the row variable. -/
  continuous_left : ∀ y ∈ Y, ContinuousOn (fun x => f x y) X
  /-- For each column point, the payoff is convex in the row variable. -/
  convex_left : ∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)
  /-- For each row point, the payoff is concave in the column variable. -/
  concave_right : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => f x y)
  /-- The payoff is bounded above on `X × Y`. -/
  bounded_above : BddAbove (Set.range fun xy : X × Y => f xy.1 xy.2)
  /-- The payoff is bounded below on `X × Y`. -/
  bounded_below : BddBelow (Set.range fun xy : X × Y => f xy.1 xy.2)
