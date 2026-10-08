import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage

/-!
# OnlineLearning.finiteUpperImage_convex

Topic: equilibria   Node: 4ebf9269d1d3

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteUpperImage_convex`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convexity of the finite upper image. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff, and let $u$ be
a finite sample of columns from $Y$. If $X$ is convex and, for every $y \in Y$, the map
$x \mapsto f(x,y)$ is convex on $X$, then the finite upper image $U(X,f,u)$ is a convex
subset of $u \to \bbr$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper image of a finite column sample is convex when `X` is convex and `f` is convex in the row variable: if `z` is witnessed by the row `x` and `w` by the row `x'`, then the convex combination `a z + b w` is witnessed by the row `a x + b x'`, since convexity of `f` in the row variable gives `f (a x + b x') y ≤ a f x y + b f x' y`. **Proof sketch.** Let `z` be witnessed by the row `x` and `w` by the row `x'`, and let `a, b ≥ 0` with `a + b = 1`. Step 1: the row `a x + b x'` lies in `X` by convexity of `X`. Step 2: for each sampled column `y`, convexity of `f(·, y)` on `X` gives `f (a x + b x') y ≤ a f x y + b f x' y`. Step 3: the strict witness inequalities `f x y < z y` and `f x' y < w y` combine to `a f x y + b f x' y < a z y + b w y`, by cases on whether `a = 0` (so `b = 1`), `b = 0` (so `a = 1`), or both are positive (scale each inequality by its positive weight and add). Step 4: chain Steps 2 and 3. -/
lemma OnlineLearning.finiteUpperImage_convex {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} (u : Finset Y)
    (hX : Convex ℝ X) (hf : ∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) :
    Convex ℝ (finiteUpperImage X f u) := by
  intro z hz w hw a b ha hb hab
  rcases hz with ⟨x, hx, hz⟩
  rcases hw with ⟨x', hx', hw⟩
  -- Step 1: the witness row `a x + b x'` lies in `X` by convexity.
  refine ⟨a • x + b • x', hX hx hx' ha hb hab, ?_⟩
  intro y
  -- Step 2: convexity of `f(·, y)` on `X` at the two witness rows.
  have hconv := (hf (y : Y) (y : Y).2).2 hx hx' ha hb hab
  have hz_y := hz y
  have hw_y := hw y
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hconv hz_y hw_y ⊢
  -- Step 3: combine the strict witness inequalities, by cases on the weights.
  have hlt : a * f x ↑↑y + b * f x' ↑↑y < a * z y + b * w y := by
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb_one : b = 1 := by linarith
      nlinarith
    · rcases hb.eq_or_lt with rfl | hb_pos
      · have ha_one : a = 1 := by linarith
        nlinarith
      · have hz_mul := mul_lt_mul_of_pos_left hz_y ha_pos
        have hw_mul := mul_lt_mul_of_pos_left hw_y hb_pos
        nlinarith
  -- Step 4: chain Steps 2 and 3.
  exact hconv.trans_lt hlt
