import AFTD.Prelude

/-!
# CircleLocalView

Topic: combinatorial_games   Node: 224bc890fa2f

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

For sages of type α, a local view in an unlabeled circle consists of the sage's own identity together with their left neighbor and right neighbor.
-/

/-- The local view of a sage in a circle: identity, left neighbor, and right neighbor. -/
def CircleLocalView (α : Type) : Type := α × α × α
