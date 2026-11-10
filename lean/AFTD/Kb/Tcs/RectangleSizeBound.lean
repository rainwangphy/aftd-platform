import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# rectangle_size_bound

Topic: communication   Node: c792fd28d496

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.2, Equation (1.2)

For finite types $X$ and $Y$ and a curried Boolean function $f : X \to Y \to \mathrm{Bool}$, the prior-free rectangle-size bound $\mathrm{rectangle\_size\_bound}(f) \in \mathbb{R}$ is the supremum over all probability mass functions $\mu : X \times Y \to \mathbb{R}$ (satisfying $\forall p, 0 \le \mu(p)$ and $\sum_{p : X \times Y} \mu(p) = 1$) of $-\log_2$ of the supremum of $\sum_{p \in R} \mu(p)$ over all subsets $R \subseteq X \times Y$ satisfying $\mathrm{CommunicationComplexity.Rectangle.IsRectangle}\;R$ and $\mathrm{CommunicationComplexity.Rectangle.IsMonochromatic}\;R\;f$.
-/

/-- The prior-free rectangle-size bound RS₀(f) for finite input spaces. -/
noncomputable def rectangle_size_bound {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → Bool) : ℝ := open Classical in
  ⨆ (μ : X × Y → ℝ) (_ : (∀ p, 0 ≤ μ p) ∧ ∑ p : X × Y, μ p = 1),
    -Real.logb 2 (⨆ (R : Set (X × Y)) (_ : CommunicationComplexity.Rectangle.IsRectangle R ∧ CommunicationComplexity.Rectangle.IsMonochromatic R f),
      ∑ p ∈ Finset.univ.filter (fun q => q ∈ R), μ p)
