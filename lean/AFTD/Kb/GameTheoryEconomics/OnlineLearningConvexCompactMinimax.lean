import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxBySeparation
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxStatement
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses

/-!
# OnlineLearning.convex_compact_minimax

Topic: equilibria   Node: 445fb5d239cb

Provenance: formalization of a published result. Source: Convex-compact minimax theorem on the line, as formalized in TCSlib (`OnlineLearning.convex_compact_minimax`). Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimax.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex-compact minimax theorem on the line. Let $X, Y \subseteq \bbr$ be nonempty convex sets with $X$ compact, and let $f : \bbr
\times \bbr \to \bbr$ be a payoff function that is bounded above and below on $X \times
Y$. Suppose that for every $y \in Y$ the map $x \mapsto f(x,y)$ is continuous and convex
on $X$, and that for every $x \in X$ the map $y \mapsto f(x,y)$ is concave on $Y$. Then
the minimax identity holds:
\[
  \inf_{x \in X}\,\sup_{y \in Y}\, f(x,y)
  \;=\;
  \sup_{y \in Y}\,\inf_{x \in X}\, f(x,y).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The convex-compact minimax theorem: for a nonempty compact convex `X ⊆ ℝ`, a nonempty convex `Y ⊆ ℝ`, and a bounded payoff `f` that is convex and continuous in the row variable `x` for each `y ∈ Y` and concave in the column variable `y` for each `x ∈ X` (the hypotheses bundled in `ConvexCompactMinimaxHypotheses`), the upper value `inf_{x ∈ X} sup_{y ∈ Y} f x y` equals the lower value `sup_{y ∈ Y} inf_{x ∈ X} f x y` (the conclusion `ConvexCompactMinimaxStatement`). [CBL06, Thm 7.1]. Deviation: specialized to subsets of `ℝ`, and proved via the Hahn–Banach separation route of `ConvexMinimaxSeparation` rather than the source's no-regret argument, whose last step needs an extra uniformity hypothesis (see `ConvexMinimaxNoRegret`). This theorem is intentionally a thin wrapper. It hides the proof-route choice from downstream files and currently delegates to the completed separation proof. -/
theorem OnlineLearning.convex_compact_minimax {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  -- Keep the public theorem independent of proof-route details.  At present,
  -- the separation proof is the strongest completed route.
  exact convex_compact_minimax_by_separation h
