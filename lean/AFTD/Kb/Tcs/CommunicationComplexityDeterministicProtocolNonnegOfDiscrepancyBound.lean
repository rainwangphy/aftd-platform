import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDiscrepancy
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.Deterministic.Protocol.nonneg_of_discrepancy_bound

Topic: communication   Node: 7a8a51b9b9b4

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.nonneg_of_discrepancy_bound`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Discrepancy bound is nonnegative. Let $X \times Y$ carry a finite probability space $\mu$, let $g : X \to Y \to
\mathrm{Bool}$ be a Boolean function, and let $\gamma \in \bbr$. If every rectangle $R
\subseteq X \times Y$ satisfies $\abs{\mathrm{disc}_\mu(g, R)} \le \gamma$, then $\gamma
\ge 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- A uniform bound `γ` on the absolute discrepancy of all rectangles is nonnegative (apply the bound to the full rectangle `X × Y`). -/
lemma CommunicationComplexity.Deterministic.Protocol.nonneg_of_discrepancy_bound
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ) :
    0 ≤ γ := by
  have huniv :=
    hdisc Set.univ ⟨Set.univ, Set.univ, by
      ext xy
      simp⟩
  exact le_trans (abs_nonneg _) huniv
