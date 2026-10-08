import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningContinuousLinearMapPiApplyEqSumSingle
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage

/-!
# OnlineLearning.separating_functional_normalized_le

Topic: equilibria   Node: d2f8365466d5

Provenance: helper lemma. TCSlib, `OnlineLearning.separating_functional_normalized_le`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Normalized separator bounds the constant by the average payoff. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff, let $u$ be a
finite sample of columns from $Y$, and let $c \in \bbr$. Suppose $L : \bbr^u \to \bbr$
is a continuous linear functional separating the constant vector $(c,\dots,c)$ from the
finite upper image, i.e.\ $L(z) < L(c,\dots,c)$ for every $z \in U(X,f,u)$, and that
the total weight $W = \sum_{y \in u} \bigl(-L(e_y)\bigr)$ is strictly positive, where
$e_y$ is the standard basis vector at $y$. Then for every row $x \in X$,
\[
  c \;\le\; \sum_{y \in u} \frac{-L(e_y)}{W}\, f(x,y),
\]
that is, $c$ is at most the payoff of $x$ averaged under the normalized weights
$-L(e_y)/W$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The algebraic heart of the separation argument: if `L` separates the upper image of a finite column sample from the constant vector `c` (`L z < L (c, …, c)` for all `z` in the upper image) and `W = Σ_y −L(e_y) > 0`, then for every row `x ∈ X` the constant `c` is at most the average payoff `Σ_y (−L(e_y)/W) · f x y` of `x` under the normalized weights. **Proof sketch.** It suffices to show `c ≤ average + δ` for every `δ > 0`. Step 1: for a fixed row `x`, the shifted payoff vector `y ↦ f x y + δ` lies in the upper image, so separation gives `L(f x · + δ) < L(c, …, c)`. Step 2: expand both sides in coordinates via `continuousLinearMap_pi_apply_eq_sum_single`, using `Σ_y L(e_y) = −W`. Step 3: multiply the target inequality by `W > 0` and compare with Step 2's inequality. -/
lemma OnlineLearning.separating_functional_normalized_le {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {c W : ℝ} (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L (fun _ => c))
    (hW : W = ∑ y : u, -L (Pi.single y (1 : ℝ))) (hWpos : 0 < W)
    {x : ℝ} (hxX : x ∈ X) :
    c ≤ ∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) := by
  classical
  apply le_of_forall_pos_le_add
  intro δ hδ
  -- Step 1: the shifted payoff vector `f x · + δ` lies in the upper image, so
  -- separation applies to it.
  have hlt : L (fun y : u => f x (y : ℝ) + δ) < L (fun _ => c) :=
    hsep _ ⟨x, hxX, fun y => by simp [hδ]⟩
  -- Step 2: expand both sides of the separation inequality in coordinates.
  have hsum : ∑ y : u, L (Pi.single y (1 : ℝ)) = -W := by
    rw [hW, Finset.sum_neg_distrib, neg_neg]
  have hLz : L (fun y : u => f x (y : ℝ) + δ) =
      ∑ y : u, f x (y : ℝ) * L (Pi.single y (1 : ℝ)) +
        δ * ∑ y : u, L (Pi.single y (1 : ℝ)) := by
    rw [continuousLinearMap_pi_apply_eq_sum_single L, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hLc : L (fun _ : u => c) = c * ∑ y : u, L (Pi.single y (1 : ℝ)) := by
    rw [continuousLinearMap_pi_apply_eq_sum_single L, Finset.mul_sum]
  rw [hLz, hLc, hsum] at hlt
  -- Step 3: clear the denominator `W > 0` and compare.
  have hWne : W ≠ 0 := hWpos.ne'
  have hkey : c * W ≤ (∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) + δ) * W := by
    have hterm : ∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) * W =
        -(∑ y : u, f x (y : ℝ) * L (Pi.single y (1 : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [show (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) * W =
          -(f x (y : ℝ) * L (Pi.single y (1 : ℝ))) * (W / W) by ring, div_self hWne, mul_one]
    rw [add_mul, Finset.sum_mul, hterm]
    linarith
  exact le_of_mul_le_mul_right hkey hWpos
