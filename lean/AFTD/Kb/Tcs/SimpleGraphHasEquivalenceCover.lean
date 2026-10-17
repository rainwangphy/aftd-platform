import AFTD.Prelude

/-!
# simple_graph_has_equivalence_cover

Topic: combinatorics   Node: 4dbdd5e7b206

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Sec. 1 (equivalence subgraphs; the labelling c_s of components is the one used in the proofs of Lemma 2.2 and Theorem 3.4).

G can be covered by t equivalence subgraphs: there are t spanning subgraphs of G, each a disjoint union of cliques (isolated vertices allowed), whose edge sets together cover E(G). Each one is given by a labelling c_s of the vertices whose classes are cliques of G; its edges are the pairs with equal labels.
-/

/-- `G` is covered by `t` equivalence subgraphs. Subgraph `s` is the partition of `V` into the classes of the labelling `c s`; each class must be a clique of `G` (so the subgraph is a disjoint union of cliques of `G`), and every edge of `G` must join two vertices with the same label in some `c s`. Labels in `V` lose nothing: a partition of `V` has at most `|V|` classes. -/
def simple_graph_has_equivalence_cover {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ c : Fin t → V → V,
    (∀ s u v, u ≠ v → c s u = c s v → G.Adj u v) ∧
    ∀ u v, G.Adj u v → ∃ s, c s u = c s v
