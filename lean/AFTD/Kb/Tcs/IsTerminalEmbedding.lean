import AFTD.Prelude

/-!
# IsTerminalEmbedding

Topic: algorithms   Node: cfd745c5aa39

Provenance: formalization of a published result. Source: arXiv:2611.08546 "Bourgain's Theorem for a Union of Euclidean Metric Spaces", Definition 2.1

A map φ from a metric space X to a metric space H is a terminal embedding for a subset V of X if φ is 1-Lipschitz and for every x in V and every y in X, dist (φ x) (φ y) = dist x y.
-/

/-- A map φ : X → H is a terminal embedding for V ⊆ X if φ is 1-Lipschitz and preserves distances from all points in V to all points in X. -/
def IsTerminalEmbedding.{u, v} {X : Type u} {H : Type v} [MetricSpace X] [MetricSpace H]
    (V : Set X) (φ : X → H) : Prop :=
  LipschitzWith 1 φ ∧ ∀ x ∈ V, ∀ y : X, dist (φ x) (φ y) = dist x y
