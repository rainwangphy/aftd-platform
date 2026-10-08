import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImageNonempty

/-!
# OnlineLearning.separating_functional_ne_zero

Topic: equilibria   Node: fa9a9ded72df

Provenance: helper lemma. TCSlib, `OnlineLearning.separating_functional_ne_zero`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonzero separating functional over the upper image. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff, and let $u$ be
a finite sample of columns drawn from $Y$, with $X$ nonempty. Fix a vector $c : u \to
\bbr$ and a continuous linear functional $L : (u \to \bbr) \to \bbr$. If $L(z) < L(c)$
for every $z$ in the finite upper image $U(X,f,u)$, then $L$ is not the zero functional.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A functional separating the (nonempty) upper image from a point is nonzero: the zero functional cannot be strictly smaller on every upper-image point than on `cvec`. -/
lemma OnlineLearning.separating_functional_ne_zero {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    L ≠ 0 := by
  intro hL
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  simpa [hL] using hsep z hz
