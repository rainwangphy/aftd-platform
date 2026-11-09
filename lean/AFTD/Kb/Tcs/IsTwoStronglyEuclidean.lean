import AFTD.Prelude

/-!
# IsTwoStronglyEuclidean

Topic: algorithms   Node: 1a7dd0868df7

Provenance: formalization of a published result. Source: arXiv:2611.08546 "Bourgain's Theorem for a Union of Euclidean Metric Spaces", Section 1.1

A subset V of a metric space X is 2-strongly Euclidean in X if for every x, y in X, there exists a real Hilbert space H and an isometry from V ∪ {x, y} into H.
-/

/-- A subset V of a metric space X is 2-strongly Euclidean in X if for every pair x, y ∈ X, the subset V ∪ {x, y} embeds isometrically into a real Hilbert space. -/
def IsTwoStronglyEuclidean.{u} {X : Type u} [MetricSpace X] (V : Set X) : Prop :=
  ∀ x y : X, ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H),
    ∃ f : (V ∪ {x, y} : Set X) → H, Isometry f
