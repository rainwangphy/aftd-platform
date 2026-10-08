import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMinimaxSublevel
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImage
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImageConvex
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperImageIsOpen
import AFTD.Kb.GameTheoryEconomics.OnlineLearningSeparatingCoordinateNonpos
import AFTD.Kb.GameTheoryEconomics.OnlineLearningSeparatingFunctionalNormalizedLe
import AFTD.Kb.GameTheoryEconomics.OnlineLearningSeparatingWeightSumPos
import AFTD.Kb.Tcs.Regret

/-!
# OnlineLearning.finite_sublevel_intersections_by_separation

Topic: equilibria   Node: fec40cb21a0e

Provenance: helper lemma. TCSlib, `OnlineLearning.finite_sublevel_intersections_by_separation`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonempty finite intersection of minimax sublevel sets. Let $X, Y \subseteq \bbr$ and $f : \bbr \times \bbr \to \bbr$ satisfy the convex-compact
minimax hypotheses, and write $v = \sup_{y \in Y} \inf_{x \in X} f(x,y)$ for the lower
value of the payoff. Then for every $\varepsilon > 0$ and every finite set $u$ of
columns chosen from $Y$, there is a row $x \in X$ with $f(x,y) \le v + \varepsilon$
simultaneously for all $y \in u$; equivalently, the intersection over $y \in u$ of the
sublevel sets $\{x \in X : f(x,y) \le v + \varepsilon\}$ is nonempty.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The key separation lemma: under `ConvexCompactMinimaxHypotheses`, for every `ε > 0` and every finite set `u` of column points, there is a row `x ∈ X` whose payoff is at most `v + ε` on all columns in `u`, where `v = sup_{y ∈ Y} inf_{x ∈ X} f x y` is the lower value. [CBL06, Thm 7.1]. Deviation: proved by Hahn–Banach separation on the finite column sample rather than by the source's no-regret argument (see the module docstring). **Proof sketch.** Let `c := v + ε` and `cvec` the constant vector `c` on `u`. Step 1 (trivial case): if `cvec` lies in the upper image of `u`, its witness row has `f x y < c` on every sampled column. Step 2 (Hahn–Banach): otherwise `geometric_hahn_banach_open_point` separates the open convex upper image from `cvec` by a functional `L` with `L z < L cvec` on the upper image. Step 3: the normalized negated coefficients `q y := −L(e_y)/W`, with `W = Σ_y −L(e_y) > 0`, form a mixed column strategy on `u` (`hWpos`, `hq_nonneg`, `hq_sum`). Step 4 (`hsep_le`): by `separating_functional_normalized_le`, `c ≤ Σ_y q y · f x y` for every row `x ∈ X`. Step 5: the `q`-average `ȳ := Σ_y q y · y` lies in `Y` by convexity. Step 6 (Jensen): concavity in the column variable gives `Σ_y q y · f x y ≤ f x ȳ`, hence `c ≤ f x ȳ` for all `x ∈ X`. Step 7 (contradiction): `c ≤ inf_x f x ȳ ≤ v`, contradicting `c = v + ε`. -/
lemma OnlineLearning.finite_sublevel_intersections_by_separation {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ∀ ε > 0, ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u,
        minimaxSublevel X f (y : ℝ) ((⨆ y : Y, ⨅ x : X, f x y) + ε)).Nonempty := by
  classical
  intro ε hε u
  let v : ℝ := ⨆ y : Y, ⨅ x : X, f x y
  let c : ℝ := v + ε
  let cvec : u → ℝ := fun _ => c
  by_cases hc : cvec ∈ finiteUpperImage X f u
  -- Step 1 (trivial case): membership of the constant vector gives a row with
  -- `f x y < c` on every sampled column, which is stronger than the sublevel
  -- condition we need.
  · rcases hc with ⟨x, hxX, hxlt⟩
    refine ⟨x, hxX, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro y
    refine Set.mem_iInter.mpr ?_
    intro hyu
    exact ⟨hxX, (hxlt ⟨y, hyu⟩).le⟩
  -- Step 2 (Hahn–Banach): the constant vector is outside the open convex upper
  -- image.  Separation gives a functional `L`; the previous lemmas show that
  -- `-L(e_y)` can be normalized into weights on the sampled columns.
  · obtain ⟨L, hsep⟩ :=
      geometric_hahn_banach_open_point
        (finiteUpperImage_convex (X := X) (Y := Y) (f := f) u h.X_convex h.convex_left)
        (finiteUpperImage_isOpen (X := X) (Y := Y) (f := f) u) hc
    -- Step 3: the normalized coefficients `q` form a mixed column strategy.
    let W : ℝ := ∑ y : u, -L (Pi.single y (1 : ℝ))
    have hWpos : 0 < W :=
      separating_weight_sum_pos (X := X) (Y := Y) (f := f) h.X_nonempty L hsep
    let q : u → ℝ := fun y => -L (Pi.single y (1 : ℝ)) / W
    have hcoord_nonpos :
        ∀ y : u, L (Pi.single y (1 : ℝ)) ≤ 0 :=
      separating_coordinate_nonpos (X := X) (Y := Y) (f := f) h.X_nonempty L hsep
    have hq_nonneg : ∀ y : u, 0 ≤ q y := by
      intro y
      exact div_nonneg (by linarith [hcoord_nonpos y]) hWpos.le
    have hq_sum : ∑ y : u, q y = 1 := by
      calc
        ∑ y : u, q y = (∑ y : u, -L (Pi.single y (1 : ℝ))) / W := by
          simp [q, div_eq_mul_inv, Finset.sum_mul]
        _ = W / W := rfl
        _ = 1 := div_self hWpos.ne'
    -- Step 4: the algebraic heart — separation, expanded in coordinates and
    -- normalized by `W`, bounds `c` by the `q`-average payoff of every row.
    have hsep_le : ∀ x ∈ X, c ≤ ∑ y : u, q y * f x (y : ℝ) := fun x hxX =>
      separating_functional_normalized_le (c := c) L hsep rfl hWpos hxX
    -- Step 5: the weights `q` are a probability distribution on the sampled
    -- columns.  Convexity of `Y` makes their weighted average `ybar` an actual point of
    -- `Y`, and concavity in the column variable gives Jensen's inequality:
    -- average payoff at the sampled columns is at most payoff at `ybar`.
    let ybar : ℝ := ∑ y : u, q y * (y : ℝ)
    have hybar : ybar ∈ Y := by
      simpa [ybar, smul_eq_mul] using
        h.Y_convex.sum_mem (t := Finset.univ) (w := q) (z := fun y : u => (y : ℝ))
          (fun y _ => hq_nonneg y) (by simpa using hq_sum) (fun y _ => (y : Y).2)
    -- Step 6 (Jensen): concavity in the column variable lifts the bound to `ybar`.
    have hforall_x : ∀ x : X, c ≤ f x ybar := by
      intro x
      have hleft := hsep_le (x : ℝ) x.2
      have hconc :
          (∑ y : u, q y * f (x : ℝ) (y : ℝ)) ≤ f (x : ℝ) ybar := by
        simpa [ybar, smul_eq_mul] using
          (h.concave_right (x : ℝ) x.2).le_map_sum
            (t := Finset.univ) (w := q) (p := fun y : u => (y : ℝ))
            (fun y _ => hq_nonneg y) (by simpa using hq_sum) (fun y _ => (y : Y).2)
      exact hleft.trans hconc
    -- Step 7 (contradiction): the same column `ybar` satisfies `c ≤ f x ybar`
    -- for every row.
    -- Hence `c ≤ inf_x f x ybar ≤ sup_y inf_x f x y = v`, contradicting
    -- `c = v + ε`.
    have hinf : c ≤ ⨅ x : X, f x ybar := by
      haveI : Nonempty X := h.X_nonempty.to_subtype
      exact le_ciInf hforall_x
    have hbddAbove_inf : BddAbove (Set.range fun y : Y => ⨅ x : X, f x y) := by
      rcases h.bounded_above with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rintro _ ⟨y, rfl⟩
      have hbelow_y : BddBelow (Set.range fun x : X => f x y) := by
        rcases h.bounded_below with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact ha ⟨(x, y), rfl⟩
      exact (ciInf_le hbelow_y (Classical.choice h.X_nonempty.to_subtype)).trans
        (hb ⟨(Classical.choice h.X_nonempty.to_subtype, y), rfl⟩)
    have hle_v : c ≤ v := by
      let hybar_sub : Y := ⟨ybar, hybar⟩
      exact hinf.trans (le_ciSup hbddAbove_inf hybar_sub)
    have : v + ε ≤ v := by simpa [c] using hle_v
    linarith
