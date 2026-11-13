import AFTD.Prelude

/-!
# walkLengthENN

Topic: graphs   Node: e7869e4a2bf3

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

The length of a walk represented as a list of edges p : List E under edge-length function ℓ : E → ENNReal, defined as (p.map ℓ).sum.
-/

/-- The length of an edge list under edge lengths in ENNReal. -/
def walkLengthENN {E : Type*} (ℓ : E → ENNReal) (p : List E) : ENNReal :=
  (p.map ℓ).sum
