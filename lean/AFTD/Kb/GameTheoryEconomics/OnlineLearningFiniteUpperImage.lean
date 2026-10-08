import AFTD.Prelude

/-!
# OnlineLearning.finiteUpperImage

Topic: equilibria   Node: b5e2dc00481b

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.finiteUpperImage`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For sets $X, Y \subseteq \bbr$, a payoff $f : \bbr \to \bbr \to \bbr$, and a finite
sample $u$ of columns from $Y$, the finite upper image is the set
\[
  U(X,f,u) \;=\; \{\, z : u \to \bbr \;\mid\; \exists\, x \in X,\ \forall y \in u,\ f(x,y) < z_y \,\}
\]
of vectors that strictly dominate the payoff vector of some row on the sample $u$.
This set is written $\texttt{OnlineLearning.finiteUpperImage}$ in Lean.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper image of a finite column sample `u`: the set of vectors `z : u → ℝ` that lie strictly above the payoff vector `y ↦ f x y` of some row `x ∈ X` in every sampled coordinate. -/
def OnlineLearning.finiteUpperImage {Y : Set ℝ} (X : Set ℝ) (f : ℝ → ℝ → ℝ) (u : Finset Y) :
    Set (u → ℝ) :=
  {z | ∃ x ∈ X, ∀ y : u, f x y < z y}
