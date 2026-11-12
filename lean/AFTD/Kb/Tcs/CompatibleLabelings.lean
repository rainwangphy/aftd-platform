import AFTD.Prelude

/-!
# compatible_labelings

Topic: online_algorithms   Node: a680c353c5a6

Provenance: formalization of a published result. Source: arXiv:2611.13571, Section 5.1

For a simple graph G on vertex set Fin n with decidable adjacency, and a finite set H of observed edges (H : Finset (Sym2 (Fin n))), compatible_labelings G H is the number of permutations π : Equiv.Perm (Fin n) such that H is a subset of (G.map π.toEmbedding).edgeFinset.
-/

/-- The number of vertex labelings compatible with the observed edges H. -/
def compatible_labelings {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) : ℕ :=
  (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
    H ⊆ (G.map π.toEmbedding).edgeFinset)).card
