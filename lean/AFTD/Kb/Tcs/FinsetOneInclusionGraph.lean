import AFTD.Prelude

/-!
# finset_one_inclusion_graph

Topic: combinatorics   Node: 0ee5ec1b6e9a

Provenance: formalization of a published result. Source: arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Sec. 2.2 (one-inclusion graph G_1(F), before Lemma 2). Vertices are the members of 𝓕 (a subtype).

The one-inclusion graph G_1(F) of a set system F: its vertices are the members of F, two members adjacent when their symmetric difference has exactly one element.
-/

/-- The one-inclusion graph of a set system: its members are the vertices, and two members are adjacent when their symmetric difference has exactly one element. -/
def finset_one_inclusion_graph {α : Type*} [DecidableEq α] (𝓕 : Finset (Finset α)) :
    SimpleGraph 𝓕 where
  Adj A B := (symmDiff (A : Finset α) B).card = 1
  symm := ⟨fun A B (h : (symmDiff (A : Finset α) B).card = 1) => by rwa [symmDiff_comm]⟩
  loopless := ⟨fun A (h : (symmDiff (A : Finset α) A).card = 1) => by simp at h⟩
