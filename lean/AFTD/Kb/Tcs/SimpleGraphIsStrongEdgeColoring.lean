import AFTD.Prelude

/-!
# simple_graph_is_strong_edge_coloring

Topic: graphs   Node: 9b41a88aaa72

Provenance: formalization of a published result. Source: arXiv:2610.41950 (Strong edge-colourings of truncations of cubic graphs), Section 1: definition of strong edge-colouring and strong conflict

For a simple graph G on W and a colour map χ : Sym2 W → Ω (a colour for each unordered pair; only its values on edges of G matter), χ is a strong edge-colouring of G: for all x, y ∈ G.edgeSet with x ≠ y that are in strong conflict -- they share an endpoint (∃ a, a ∈ x ∧ a ∈ y), or some endpoint a of x and some endpoint b of y are adjacent in G -- we have χ x ≠ χ y. Equivalently, distinct edges at distance at most two in the line graph get distinct colours.
-/

def simple_graph_is_strong_edge_coloring {W Ω : Type*} (G : SimpleGraph W) (χ : Sym2 W → Ω) :
    Prop :=
  ∀ x ∈ G.edgeSet, ∀ y ∈ G.edgeSet, x ≠ y →
    ((∃ a, a ∈ x ∧ a ∈ y) ∨ ∃ a b, a ∈ x ∧ b ∈ y ∧ G.Adj a b) → χ x ≠ χ y
