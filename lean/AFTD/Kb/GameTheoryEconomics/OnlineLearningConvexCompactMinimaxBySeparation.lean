import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxStatement
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxOfFiniteSublevelIntersections
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteSublevelIntersectionsBySeparation

/-!
# OnlineLearning.convex_compact_minimax_by_separation

Topic: equilibria   Node: 9c2c9b04e6a4

Provenance: helper lemma. TCSlib, `OnlineLearning.convex_compact_minimax_by_separation`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A convex–concave minimax equality. Let $X, Y \subseteq \bbr$ be nonempty sets with $X$ compact and both $X$ and $Y$ convex,
and let $f : \bbr \times \bbr \to \bbr$ be a payoff function that is bounded above and
below on $X \times Y$. Suppose that for every $y \in Y$ the section $x \mapsto f(x,y)$
is continuous and convex on $X$, while for every $x \in X$ the section $y \mapsto
f(x,y)$ is concave on $Y$. Then the minimax equality
\[
  \inf_{x \in X}\,\sup_{y \in Y} f(x,y)
  \;=\;
  \sup_{y \in Y}\,\inf_{x \in X} f(x,y)
\]
holds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The convex-compact minimax theorem via the separation route: under `ConvexCompactMinimaxHypotheses` (nonempty compact convex `X ⊆ ℝ`, nonempty convex `Y ⊆ ℝ`, bounded `f` continuous and convex in the row variable, concave in the column variable), the upper value `inf_x sup_y f x y` equals the lower value `sup_y inf_x f x y`. [CBL06, Thm 7.1]. Deviation: specialized to `ℝ`, and proved by Hahn–Banach separation on finite column samples plus compactness rather than by the source's regret-based route (whose last step is isolated, and proved under strengthened hypotheses, in `ConvexMinimaxNoRegret`); [Kom88] is a different route to a more general result, and this file does not follow Komiya's argument either. -/
theorem OnlineLearning.convex_compact_minimax_by_separation {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  exact convex_compact_minimax_of_finite_sublevel_intersections h
    (finite_sublevel_intersections_by_separation h)
