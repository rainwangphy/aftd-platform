import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMinimaxSublevel
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMinimaxSublevelIsClosed

/-!
# OnlineLearning.exists_forall_le_of_finite_sublevel_intersections

Topic: equilibria   Node: b8f6c0dc65b5

Provenance: helper lemma. TCSlib, `OnlineLearning.exists_forall_le_of_finite_sublevel_intersections`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

From finite feasibility to a uniform row point. Let $X, Y \subseteq \bbr$ together with a payoff function $f : \bbr \to \bbr \to \bbr$
satisfy the convex-compact minimax hypotheses, and let $c \in \bbr$. Suppose that for
every finite subset $u \subseteq Y$ the set $X \cap \bigcap_{y \in u}
\mathrm{sublevel}(X,f,y,c)$ is nonempty, where $\mathrm{sublevel}(X,f,y,c) = X \cap \{x
\in \bbr : f(x,y) \le c\}$; that is, there is a common row point $x \in X$ with $f(x,y)
\le c$ for all $y$ in that finite set. Then there exists a single $x \in X$ with $f(x,y)
\le c$ for every $y \in Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The finite-intersection compactness step: under `ConvexCompactMinimaxHypotheses`, if for every finite set `u` of column points there is a point of `X` with `f x y ≤ c` for all `y ∈ u`, then there is a single point `x ∈ X` with `f x y ≤ c` for every `y ∈ Y`. This is the finite intersection property of the compact set `X` applied to the closed sublevel sets `minimaxSublevel X f y c`. -/
lemma OnlineLearning.exists_forall_le_of_finite_sublevel_intersections {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f) (c : ℝ)
    (hfin : ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u, minimaxSublevel X f y c).Nonempty) :
    ∃ x ∈ X, ∀ y : Y, f x y ≤ c := by
  have hclosed : ∀ y : Y, IsClosed (minimaxSublevel X f y c) := by
    intro y
    exact minimaxSublevel_isClosed h.X_compact.isClosed (h.continuous_left y y.2)
  rcases h.X_compact.inter_iInter_nonempty
      (fun y : Y => minimaxSublevel X f y c) hclosed hfin with ⟨x, hx⟩
  refine ⟨x, hx.1, ?_⟩
  intro y
  -- Membership in every sublevel set is exactly the pointwise bound `f x y ≤ c`.
  exact (Set.mem_iInter.mp hx.2 y).2
