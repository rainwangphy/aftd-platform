import AFTD.Prelude

/-!
# SkewZeroForced

Topic: graphs   Node: 223fa4f391df

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 1 and Section 2

The skew zero forcing closure predicate on vertices V: a vertex is forced from an initial set S under neighborhood function N if it is in S or if it is the unique unfilled neighbor of some vertex u.
-/

/-- Inductive definition of the skew zero forcing closure of an initial set under the skew color change rule. -/
inductive SkewZeroForced {V : Type*} (N : V → Set V) (S : Set V) : V → Prop where
  | init (v : V) : v ∈ S → SkewZeroForced N S v
  | step (u : V) (w : V) :
      w ∈ N u →
      (∀ x ∈ N u, x ≠ w → SkewZeroForced N S x) →
      SkewZeroForced N S w
