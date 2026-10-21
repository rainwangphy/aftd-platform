import AFTD.Prelude

/-!
# is_globally_best_outside

Topic: algorithms   Node: 55619e1ce997

Provenance: formalization of a published result. Source: arXiv:2610.23032 Definition 1

Given a simple graph G on V, an ordinal profile π : V → LinearOrder V, and vertices r, g : V, is_globally_best_outside G π r g holds if g does not belong to the same connected component of G as r, and for every vertex v not in the same connected component of G as r, g ≤ v according to the linear order π r.
-/

/-- Vertex g is the globally best outside vertex of r if it is outside r's component and is r's most preferred outside vertex. -/
def is_globally_best_outside {V : Type*} (G : SimpleGraph V) (π : V → LinearOrder V) (r g : V) : Prop :=
  G.connectedComponentMk g ≠ G.connectedComponentMk r ∧
  ∀ v : V, G.connectedComponentMk v ≠ G.connectedComponentMk r → (π r).le g v
