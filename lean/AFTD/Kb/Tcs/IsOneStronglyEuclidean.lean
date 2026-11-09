import AFTD.Prelude

/-!
# IsOneStronglyEuclidean

Topic: algorithms   Node: 35c6517c946f

Provenance: formalization of a published result. Source: arXiv:2611.08546, Sec. 1.1, p. 3

A subset U of a metric space X is 1-strongly Euclidean in X if for every point x in X, there exists a real Hilbert space H and an isometry from U ∪ {x} into H.
-/

/-- A subset U is 1-strongly Euclidean if adding any point x yields a set that isometrically embeds into a Hilbert space. -/
def IsOneStronglyEuclidean.{u} {X : Type u} [MetricSpace X] (U : Set X) : Prop :=
  ∀ x : X, ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H),
    ∃ f : (U ∪ {x} : Set X) → H, Isometry f
