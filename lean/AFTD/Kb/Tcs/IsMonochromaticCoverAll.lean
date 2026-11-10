import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic

/-!
# is_monochromatic_cover_all

Topic: communication   Node: 873da566587a

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1

Given types $X$ and $Y$ and a curried Boolean function $f : X \to Y \to \mathrm{Bool}$, a collection $C : \mathrm{Set}\;(\mathrm{Set}\;(X \times Y))$ is a monochromatic rectangle cover of all inputs for $f$ if every $R \in C$ satisfies $\mathrm{CommunicationComplexity.Rectangle.IsRectangle}\;R$, every $R \in C$ satisfies $\mathrm{CommunicationComplexity.Rectangle.IsMonochromatic}\;R\;f$, and $\bigcup C = \mathrm{Set.univ}$.
-/

/-- Predicate stating that C is a monochromatic rectangle cover of all inputs. -/
def is_monochromatic_cover_all {X Y : Type*} (C : Set (Set (X × Y))) (f : X → Y → Bool) : Prop :=
  (∀ R ∈ C, CommunicationComplexity.Rectangle.IsRectangle R) ∧
  (∀ R ∈ C, CommunicationComplexity.Rectangle.IsMonochromatic R f) ∧
  ⋃₀ C = Set.univ
