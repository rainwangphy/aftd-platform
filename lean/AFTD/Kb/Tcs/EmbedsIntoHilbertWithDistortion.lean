import AFTD.Prelude

/-!
# EmbedsIntoHilbertWithDistortion

Topic: algorithms   Node: aefa14897972

Provenance: formalization of a published result. Source: arXiv:2611.08546, Sec. 1.1, Eq. (1)

A metric space X embeds into a real Hilbert space with distortion at most D if there exists a real Hilbert space H and a map f from X to H such that dist x y ≤ dist (f x) (f y) ≤ D * dist x y for all x, y in X.
-/

/-- A metric space X embeds into a real Hilbert space with distortion at most D. -/
def EmbedsIntoHilbertWithDistortion.{u} (X : Type u) [MetricSpace X] (D : ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H),
    ∃ f : X → H, ∀ x y : X, dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ D * dist x y
