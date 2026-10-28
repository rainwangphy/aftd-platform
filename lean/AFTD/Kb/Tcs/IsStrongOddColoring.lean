import AFTD.Prelude

/-!
# is_strong_odd_coloring

Topic: graphs   Node: cb7e452be53e

Provenance: formalization of a published result. Source: arXiv:2610.34874

A vertex coloring f : V → κ of a finite simple graph G is a strong odd coloring if it is proper and, for every vertex v and every color c, the number of neighbors of v colored c is either zero or odd.
-/

/-- A proper coloring where each color appearing on the neighborhood of any vertex appears an odd number of times. -/
def is_strong_odd_coloring {V κ : Type*} [Fintype V] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → κ) : Prop := (∀ {u v : V}, G.Adj u v → f u ≠ f v) ∧
  ∀ (v : V) (c : κ),
    (G.neighborFinset v).filter (fun u => f u = c) = ∅ ∨
    Odd ((G.neighborFinset v).filter (fun u => f u = c)).card
