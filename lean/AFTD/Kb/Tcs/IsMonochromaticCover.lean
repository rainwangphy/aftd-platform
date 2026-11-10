import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# is_monochromatic_cover

Topic: communication   Node: 431d0abfe18d

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1

Given types $X$ and $Y$, a curried Boolean function $f : X \to Y \to \mathrm{Bool}$, and a Boolean value $b : \mathrm{Bool}$, a collection $C : \mathrm{Set}\;(\mathrm{Set}\;(X \times Y))$ is a $b$-monochromatic rectangle cover of $f^{-1}(b)$ if every $R \in C$ satisfies $\mathrm{CommunicationComplexity.Rectangle.IsRectangle}\;R$, for every $R \in C$ and $(x,y) \in R$ we have $f\;x\;y = b$, and $\{p : X \times Y \mid f\;p.1\;p.2 = b\} \subseteq \bigcup C$.
-/

/-- Predicate stating that C is a collection of b-monochromatic rectangles covering f⁻¹(b). -/
def is_monochromatic_cover {X Y : Type*} (C : Set (Set (X × Y))) (f : X → Y → Bool) (b : Bool) : Prop :=
  (∀ R ∈ C, CommunicationComplexity.Rectangle.IsRectangle R) ∧
  (∀ R ∈ C, ∀ x y, (x, y) ∈ R → f x y = b) ∧
  {p : X × Y | f p.1 p.2 = b} ⊆ ⋃₀ C
