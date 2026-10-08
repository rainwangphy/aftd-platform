import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage

/-!
# OnlineLearning.finiteUpperImage_isOpen

Topic: equilibria   Node: 8542974c82c9

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteUpperImage_isOpen`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finite upper image is open. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff function, and
let $u$ be a finite sample of columns from $Y$. Then the finite upper image
\[
U(X,f,u) \;=\; \{\, z : u \to \bbr \;\mid\; \exists\, x \in X,\ \forall y \in u,\ f(x,y)
< z_y \,\}
\]
is an open subset of the space $u \to \bbr$ of vectors indexed by $u$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper image of a finite column sample is open in the product topology: for a fixed row `x`, membership is finitely many strict inequalities `f x y < z y`, each an open condition, and the upper image is the union of these open sets over `x ∈ X`. -/
lemma OnlineLearning.finiteUpperImage_isOpen {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} (u : Finset Y) :
    IsOpen (finiteUpperImage X f u) := by
  classical
  have hrepr :
      finiteUpperImage X f u =
        ⋃ x : X,
          ({z : u → ℝ | ∀ y : u, f (x : ℝ) (y : ℝ) < z y} : Set (u → ℝ)) := by
    ext z
    simp [finiteUpperImage]
  rw [hrepr]
  apply isOpen_iUnion
  intro x
  rw [show ({z : u → ℝ | ∀ y : u, f (x : ℝ) (y : ℝ) < z y} : Set (u → ℝ)) =
      ⋂ y : u, (fun z : u → ℝ => z y) ⁻¹' Set.Ioi (f (x : ℝ) (y : ℝ)) by
    ext z
    simp]
  exact isOpen_iInter_of_finite fun y : u =>
    isOpen_Ioi.preimage (continuous_apply y)
