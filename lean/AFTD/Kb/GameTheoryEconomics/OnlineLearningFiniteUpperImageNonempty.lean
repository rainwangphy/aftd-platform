import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage

/-!
# OnlineLearning.finiteUpperImage_nonempty

Topic: equilibria   Node: c1711c19183c

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteUpperImage_nonempty`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonemptiness of the finite upper image. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff function, and
let $u$ be a finite sample of columns from $Y$. If $X$ is nonempty, then the finite
upper image $U(X,f,u)$ is nonempty; that is, there exists a vector $z : u \to \bbr$ for
which some $x \in X$ satisfies $f(x,y) < z_y$ for every $y \in u$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper image of a finite column sample is nonempty when `X` is: pick any row and add `1` to each sampled payoff. -/
lemma OnlineLearning.finiteUpperImage_nonempty {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hX : X.Nonempty) (u : Finset Y) :
    (finiteUpperImage X f u).Nonempty := by
  rcases hX with ⟨x, hx⟩
  refine ⟨fun y : u => f x y + 1, x, hx, ?_⟩
  intro y
  linarith
