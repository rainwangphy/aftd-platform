import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage

/-!
# OnlineLearning.finiteUpperImage_upper

Topic: equilibria   Node: 40ade7d48b56

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteUpperImage_upper`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite upper image is upward closed. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff, and let $u$ be
a finite sample of columns from $Y$. If a vector $z : u \to \bbr$ belongs to the finite
upper image $U(X,f,u)$, and $z' : u \to \bbr$ satisfies $z_y \le z'_y$ for every $y \in
u$, then $z'$ also belongs to $U(X,f,u)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper image is coordinatewise upward closed: increasing any coordinates of a member keeps it in the upper image, with the same witness row. -/
lemma OnlineLearning.finiteUpperImage_upper {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {z : u → ℝ} (hz : z ∈ finiteUpperImage X f u) {z' : u → ℝ}
    (hzz' : ∀ y : u, z y ≤ z' y) :
    z' ∈ finiteUpperImage X f u := by
  rcases hz with ⟨x, hx, hz⟩
  exact ⟨x, hx, fun y => (hz y).trans_le (hzz' y)⟩
