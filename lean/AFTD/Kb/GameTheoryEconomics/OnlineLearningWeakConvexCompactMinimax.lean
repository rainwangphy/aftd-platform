import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses

/-!
# OnlineLearning.weak_convex_compact_minimax

Topic: equilibria   Node: 9c74c0a980d1

Provenance: helper lemma. TCSlib, `OnlineLearning.weak_convex_compact_minimax`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weak minimax inequality for convex-compact games. Let $X, Y \subseteq \bbr$ be nonempty convex sets with $X$ also compact, and let $f : X
\times Y \to \bbr$ be a payoff that is bounded above and below on $X \times Y$, such
that for every $y \in Y$ the map $x \mapsto f(x,y)$ is continuous and convex on $X$, and
for every $x \in X$ the map $y \mapsto f(x,y)$ is concave on $Y$. Then
\[
  \sup_{y \in Y}\,\inf_{x \in X}\, f(x,y)
  \;\leq\;
  \inf_{x \in X}\,\sup_{y \in Y}\, f(x,y).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Weak duality for convex-compact games: under `ConvexCompactMinimaxHypotheses`, the lower value `sup_{y ∈ Y} inf_{x ∈ X} f x y` is at most the upper value `inf_{x ∈ X} sup_{y ∈ Y} f x y`. [CBL06, §7.2 (weak duality)]. For every fixed pair `(x, y)`, the infimum at `y` is at most `f x y`, which is at most the supremum at `x`; taking `sup` over `y` and then `inf` over `x` preserves the inequality. -/
lemma OnlineLearning.weak_convex_compact_minimax {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    (⨆ y : Y, ⨅ x : X, f x y) ≤ (⨅ x : X, ⨆ y : Y, f x y) := by
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  apply ciSup_le
  intro y
  apply le_ciInf
  intro x
  have hbelow_y : BddBelow (Set.range fun x' : X => f x' y) := by
    rcases h.bounded_below with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rintro _ ⟨x', rfl⟩
    exact ha ⟨(x', y), rfl⟩
  have habove_x : BddAbove (Set.range fun y' : Y => f x y') := by
    rcases h.bounded_above with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨y', rfl⟩
    exact hb ⟨(x, y'), rfl⟩
  exact (ciInf_le hbelow_y x).trans (le_ciSup habove_x y)
