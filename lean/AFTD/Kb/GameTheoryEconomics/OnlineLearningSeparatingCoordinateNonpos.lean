import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImageNonempty
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImageUpper

/-!
# OnlineLearning.separating_coordinate_nonpos

Topic: equilibria   Node: 88945dfb084a

Provenance: helper lemma. TCSlib, `OnlineLearning.separating_coordinate_nonpos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Separating functional is coordinatewise nonpositive. Let $X, Y \subseteq \bbr$, let $f : \bbr \to \bbr \to \bbr$ be a payoff, let $u$ be a
finite sample of columns from $Y$, and let $c : u \to \bbr$ be a fixed vector. Suppose
$X$ is nonempty and $L : (u \to \bbr) \to \bbr$ is a continuous linear functional such
that $L(z) < L(c)$ for every $z$ in the finite upper image $U(X,f,u)$. Then for each
coordinate $y \in u$ one has $L(e_y) \le 0$, where $e_y \in (u \to \bbr)$ is the
standard basis vector taking the value $1$ at $y$ and $0$ elsewhere.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- If the functional `L` separates the upper image of a finite column sample from the point `cvec` (`L z < L cvec` for every `z` in the upper image), then no coordinate coefficient `L(e_y)` of `L` is positive. **Proof sketch.** Suppose `L(e_y) > 0` for some sampled column `y`. Step 1: take any point `z` of the (nonempty) upper image and the step size `t := (L cvec − L z + 1) / L(e_y) ≥ 0`. Step 2: `z + t e_y` still lies in the upper image by upward closedness. Step 3: by linearity `L(z + t e_y) = L cvec + 1`, contradicting separation. -/
lemma OnlineLearning.separating_coordinate_nonpos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    ∀ y : u, L (Pi.single y (1 : ℝ)) ≤ 0 := by
  classical
  intro y
  by_contra hnot
  have hpos : 0 < L (Pi.single y (1 : ℝ)) := lt_of_not_ge hnot
  -- Step 1: a point of the upper image and a nonnegative step size `t`.
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  let t := (L cvec - L z + 1) / L (Pi.single y (1 : ℝ))
  have ht_nonneg : 0 ≤ t := by
    have hnum : 0 ≤ L cvec - L z + 1 := by
      have := hsep z hz
      linarith
    exact div_nonneg hnum hpos.le
  -- Step 2: the shifted point stays in the upper image.
  have hz' :
      z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ) ∈ finiteUpperImage X f u := by
    refine finiteUpperImage_upper hz ?_
    intro y'
    by_cases hyy' : y' = y
    · subst hyy'
      simp [ht_nonneg]
    · simp [Pi.single_eq_of_ne hyy']
  -- Step 3: its `L`-value is `L cvec + 1`, contradicting separation.
  have hlt := hsep (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) hz'
  have hcalc : L (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) = L cvec + 1 := by
    simp [t, map_add, map_smul, smul_eq_mul, hpos.ne']
    field_simp [hpos.ne']
    ring
  rw [hcalc] at hlt
  linarith
