import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningContinuousLinearMapPiApplyEqSumSingle
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage
import AFTD.Kb.GameTheoryEconomics.OnlineLearningSeparatingCoordinateNonpos
import AFTD.Kb.GameTheoryEconomics.OnlineLearningSeparatingFunctionalNeZero

/-!
# OnlineLearning.separating_weight_sum_pos

Topic: equilibria   Node: 7fe1beb328fa

Provenance: helper lemma. TCSlib, `OnlineLearning.separating_weight_sum_pos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the separator's total weight. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff function, and
let $u$ be a finite sample of columns drawn from $Y$. Suppose $X$ is nonempty, fix a
vector $c \in \bbr^u$, and let $L : \bbr^u \to \bbr$ be a continuous linear functional
that strictly separates $c$ from the finite upper image $U(X,f,u)$, in the sense that
$L(z) < L(c)$ for every $z \in U(X,f,u)$. Writing $e_y \in \bbr^u$ for the standard
basis vector supported at coordinate $y$, one then has
\[
  0 \;<\; \sum_{y \in u} \bigl(-L(e_y)\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For a functional `L` separating the upper image of a finite column sample from a point, the negated coordinate coefficients `−L(e_y)` have strictly positive total mass `Σ_y −L(e_y) > 0`; dividing by this mass turns them into a probability vector. **Proof sketch.** Step 1: every `−L(e_y)` is nonnegative by `separating_coordinate_nonpos`. Step 2: some coefficient is nonzero, since otherwise the coordinate expansion `continuousLinearMap_pi_apply_eq_sum_single` would make `L = 0`, contradicting `separating_functional_ne_zero`. Step 3: that coefficient is then strictly negative, so the sum of nonnegative terms with one positive term is positive. -/
lemma OnlineLearning.separating_weight_sum_pos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    0 < ∑ y : u, -L (Pi.single y (1 : ℝ)) := by
  classical
  -- Step 1: all negated coefficients are nonnegative.
  have hnonpos := separating_coordinate_nonpos (X := X) (Y := Y) (f := f) hX L hsep
  have hnonneg : ∀ y : u, 0 ≤ -L (Pi.single y (1 : ℝ)) := by
    intro y
    linarith [hnonpos y]
  -- Step 2: some coefficient is nonzero, else `L = 0`.
  have hne : ∃ y : u, L (Pi.single y (1 : ℝ)) ≠ 0 := by
    by_contra hnone
    have hall : ∀ y : u, L (Pi.single y (1 : ℝ)) = 0 := by
      intro y
      exact not_not.mp (by
        simpa using (show ¬ L (Pi.single y (1 : ℝ)) ≠ 0 from fun hy => hnone ⟨y, hy⟩))
    have hLzero : L = 0 := by
      ext z
      rw [continuousLinearMap_pi_apply_eq_sum_single L z]
      simp [hall]
    exact separating_functional_ne_zero (X := X) (Y := Y) (f := f) hX L hsep hLzero
  -- Step 3: that coefficient is strictly negative; the sum is positive.
  rcases hne with ⟨y, hy⟩
  have hpos_y : 0 < -L (Pi.single y (1 : ℝ)) := by
    have hle := hnonpos y
    have hlt : L (Pi.single y (1 : ℝ)) < 0 := lt_of_le_of_ne hle hy
    linarith
  exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨y, Finset.mem_univ y, hpos_y⟩
