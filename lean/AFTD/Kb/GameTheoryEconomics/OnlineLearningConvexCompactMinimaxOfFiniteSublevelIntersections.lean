import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxHypotheses
import AFTD.Kb.GameTheoryEconomics.OnlineLearningConvexCompactMinimaxStatement
import AFTD.Kb.GameTheoryEconomics.OnlineLearningExistsForallLeOfFiniteSublevelIntersections
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMinimaxSublevel
import AFTD.Kb.GameTheoryEconomics.OnlineLearningWeakConvexCompactMinimax

/-!
# OnlineLearning.convex_compact_minimax_of_finite_sublevel_intersections

Topic: equilibria   Node: ee34d7356afa

Provenance: helper lemma. TCSlib, `OnlineLearning.convex_compact_minimax_of_finite_sublevel_intersections`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Minimax equality from finite sublevel intersections. Let $X, Y \subseteq \bbr$ with $X$ and $Y$ nonempty, $X$ compact and convex, and $Y$
convex, and let $f : \bbr \times \bbr \to \bbr$ be bounded above and below on $X \times
Y$, with $f(\cdot, y)$ continuous and convex on $X$ for every $y \in Y$ and $f(x,
\cdot)$ concave on $Y$ for every $x \in X$. Write $v = \sup_{y \in Y} \inf_{x \in X}
f(x,y)$ for the lower value, and suppose that for every $\varepsilon > 0$ and every
finite set $u$ of column points from $Y$, the set
\[
  \{x \in X : f(x,y) \leq v + \varepsilon \text{ for all } y \in u\}
\]
is nonempty. Then the minimax equality
\[
  \inf_{x \in X}\,\sup_{y \in Y}\,f(x,y) \;=\; \sup_{y \in Y}\,\inf_{x \in X}\,f(x,y)
\]
holds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The minimax identity from the finite sublevel intersection property: under `ConvexCompactMinimaxHypotheses`, if for every `ε > 0` and every finite set `u` of column points some row `x ∈ X` has `f x y ≤ v + ε` for all `y ∈ u` (with `v` the lower value), then the upper and lower values coincide (`ConvexCompactMinimaxStatement`). [CBL06, Thm 7.1]. This packages the compactness argument of the source's proof. **Proof sketch.** By `le_antisymm`. Step 1 (hard direction, `upper ≤ lower`): it suffices to show `upper ≤ v + ε` for every `ε > 0`. Compactness of `X` (`exists_forall_le_of_finite_sublevel_intersections`) turns the finite-sample hypothesis into a single row `x ∈ X` with `f x y ≤ v + ε` for every `y ∈ Y`; then `sup_y f x y ≤ v + ε` (`hsup_le`) and `upper ≤ sup_y f x y` since the upper value is an infimum over rows (`hleft_le`). Step 2 (easy direction): `weak_convex_compact_minimax`. -/
theorem OnlineLearning.convex_compact_minimax_of_finite_sublevel_intersections {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hfin : ∀ ε > 0, ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u,
        minimaxSublevel X f y ((⨆ y : Y, ⨅ x : X, f x y) + ε)).Nonempty) :
    ConvexCompactMinimaxStatement X Y f := by
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  unfold ConvexCompactMinimaxStatement
  apply le_antisymm
  -- Step 1: the hard direction, by compactness and letting `ε → 0`.
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hx_le⟩ :=
      exists_forall_le_of_finite_sublevel_intersections h
        ((⨆ y : Y, ⨅ x : X, f x y) + ε) (hfin ε hε)
    let xX : X := ⟨x, hx⟩
    -- The compactness point works for all columns, so the supremum over columns
    -- at this row is at most the lower value plus `ε`.
    have hsup_le :
        (⨆ y : Y, f xX y) ≤ (⨆ y : Y, ⨅ x : X, f x y) + ε := by
      exact ciSup_le fun y => hx_le y
    have hleft_le : (⨅ x : X, ⨆ y : Y, f x y) ≤ ⨆ y : Y, f xX y := by
      have hbdd : BddBelow (Set.range fun x' : X => ⨆ y : Y, f x' y) := by
        rcases h.bounded_below with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨x', rfl⟩
        let y₀ : Y := Classical.choice ‹Nonempty Y›
        have habove : BddAbove (Set.range fun y : Y => f x' y) := by
          rcases h.bounded_above with ⟨b, hb⟩
          refine ⟨b, ?_⟩
          rintro _ ⟨y, rfl⟩
          exact hb ⟨(x', y), rfl⟩
        exact (ha ⟨(x', y₀), rfl⟩).trans (le_ciSup habove y₀)
      exact ciInf_le hbdd xX
    exact hleft_le.trans hsup_le
  -- Step 2: the reverse inequality is the standard weak minimax inequality from
  -- the core file.
  · exact weak_convex_compact_minimax h
